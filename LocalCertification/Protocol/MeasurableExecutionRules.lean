import LocalCertification.Protocol.MeasurableExecution
import LocalCertification.Protocol.Rules

/-! Causal full-record execution for arbitrary measurable settings and outcomes.
The stopped label uses the ordinary sum sigma algebra. No default outcome,
countability, nonempty-space or canonical finite-tree assumption is needed. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open LocalCertification.Information.KernelHistory
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u
variable {Z S Ω : Type u} [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]

abbrev Slot (Ω : Type u) := Unit ⊕ Ω
abbrev History (Z Ω : Type u) (n : ℕ) := FullHistory Z (Slot Ω) n

/-- A live state retains every complete setting/outcome pair and its already
chosen next setting. A stopped state carries the absorbing terminal decision. -/
abbrev State (S Ω : Type u) (n : ℕ) := Fin 2 ⊕ ((Fin n → S × Ω) × S)

def withAction {n : ℕ} (h : Fin n → S × Ω) : Action S → State S Ω n
  | Sum.inl j => Sum.inl j
  | Sum.inr s => Sum.inr (h, s)

private theorem measurable_prod_sumElim {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (f : A × B → D) (g : A × C → D) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : A × (B ⊕ C) =>
      Sum.elim (fun b => f (p.1, b)) (fun c => g (p.1, c)) p.2) := by
  convert (hf.sumElim hg).comp (MeasurableEquiv.prodSumDistrib A B C).measurable using 1
  funext p
  rcases p with ⟨a, b | c⟩ <;> rfl

theorem withAction_measurable (n : ℕ) :
    Measurable (fun p : (Fin n → S × Ω) × Action S => withAction p.1 p.2) := by
  convert measurable_prod_sumElim (fun p : (Fin n → S × Ω) × Fin 2 =>
    (Sum.inl p.2 : State S Ω n)) (fun p : (Fin n → S × Ω) × S => Sum.inr p)
    (measurable_inl.comp measurable_snd) measurable_inr using 1
  funext p
  rcases p with ⟨h, j | s⟩ <;> rfl

def historySeed : ∀ n, History Z Ω n → Z
  | 0 => id
  | n+1 => fun h => historySeed n h.1

theorem historySeed_measurable (n : ℕ) : Measurable (historySeed (Z := Z) (Ω := Ω) n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp measurable_fst

/-- Empty padding in a live slot is an inconsistent path, totalized by stopping
with decision zero. Once stopped, every possible later slot stays stopped. -/
def advance (R : RawRules Z S Ω) {n : ℕ} (z : Z) : State S Ω n → Slot Ω → State S Ω (n+1)
  | Sum.inl j, _ => Sum.inl j
  | Sum.inr _, Sum.inl _ => Sum.inl 0
  | Sum.inr (h, s), Sum.inr x =>
    let h' := Fin.snoc h (s, x)
    withAction h' (R.rule (n+1) (z, h'))

theorem advance_measurable (R : RawRules Z S Ω) (n : ℕ) :
    Measurable (fun p : (Z × State S Ω n) × Slot Ω => advance R p.1.1 p.1.2 p.2) := by
  let live : (Z × ((Fin n → S × Ω) × S)) × Slot Ω → State S Ω (n+1) :=
    fun p => advance R p.1.1 (Sum.inr p.1.2) p.2
  have hlive : Measurable live := by
    let records : (Z × ((Fin n → S × Ω) × S)) × Ω → (Fin (n+1) → S × Ω) :=
      fun p => Fin.snoc p.1.2.1 (p.1.2.2, p.2)
    have hrecords : Measurable records :=
      measurable_fin_snoc (measurable_fst.comp (measurable_snd.comp measurable_fst))
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    have hnext := (withAction_measurable (n+1)).comp
      (hrecords.prodMk ((R.measurable_rule (n+1)).comp
        ((measurable_fst.comp measurable_fst).prodMk hrecords)))
    convert measurable_prod_sumElim
      (fun _ : (Z × ((Fin n → S × Ω) × S)) × Unit => (Sum.inl 0 : State S Ω (n+1)))
      (fun p : (Z × ((Fin n → S × Ω) × S)) × Ω =>
        withAction (records p) (R.rule (n+1) (p.1.1, records p))) measurable_const hnext using 1
    funext p
    rcases p with ⟨⟨z, h, s⟩, e | x⟩ <;> rfl
  have houter : Measurable (fun p : (Z × Slot Ω) × State S Ω n =>
      Sum.elim (fun j => Sum.inl j)
        (fun v => live ((p.1.1, v), p.1.2)) p.2) := by
    exact measurable_prod_sumElim
      (fun p : (Z × Slot Ω) × Fin 2 => (Sum.inl p.2 : State S Ω (n+1)))
      (fun p : (Z × Slot Ω) × ((Fin n → S × Ω) × S) => live ((p.1.1, p.2), p.1.2))
      (measurable_inl.comp measurable_snd)
      (hlive.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst)))
  have h := houter.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst))
  convert h using 1
  funext p
  rcases p with ⟨⟨z, j | v⟩, o⟩ <;> rfl

def state (R : RawRules Z S Ω) : ∀ n, History Z Ω n → State S Ω n
  | 0 => fun z => withAction Fin.elim0 (R.rule 0 (z, Fin.elim0))
  | n+1 => fun h => advance R (historySeed n h.1) (state R n h.1) h.2

theorem state_measurable (R : RawRules Z S Ω) (n : ℕ) : Measurable (state R n) := by
  induction n with
  | zero => exact (withAction_measurable 0).comp (measurable_const.prodMk
      ((R.measurable_rule 0).comp (measurable_id.prodMk measurable_const)))
  | succ n ih =>
    exact (advance_measurable R n).comp
      (((historySeed_measurable n).comp measurable_fst).prodMk (ih.comp measurable_fst) |>.prodMk measurable_snd)

def active (R : RawRules Z S Ω) (n : ℕ) : Set (History Z Ω n) :=
  {h | ∃ v, state R n h = Sum.inr v}

theorem active_measurable (R : RawRules Z S Ω) (n : ℕ) : MeasurableSet (active R n) := by
  have h := (state_measurable R n) measurableSet_range_inr
  simpa only [active, Set.preimage, Set.mem_range, eq_comm] using h

def decision {n : ℕ} : State S Ω n → Fin 2 := Sum.elim id (fun _ => 0)

theorem decision_measurable (n : ℕ) : Measurable (decision (S := S) (Ω := Ω) (n := n)) :=
  measurable_id.sumElim measurable_const

theorem state_absorbing (R : RawRules Z S Ω) {n : ℕ} (h : History Z Ω n)
    (j : Fin 2) (hj : state R n h = Sum.inl j) (o : Slot Ω) :
    state R (n+1) (h, o) = Sum.inl j := by
  change advance R _ (state R n h) o = _
  rw [hj]
  rfl

def stateKernel (K : Kernel S Ω) (n : ℕ) : Kernel (State S Ω n) (Slot Ω) where
  toFun := Sum.elim (fun _ => Measure.dirac (Sum.inl ())) (fun v => (K.map Sum.inr) v.2)
  measurable' := measurable_const.sumElim ((K.map Sum.inr).measurable.comp measurable_snd)

instance stateKernel_markov (K : Kernel S Ω) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (stateKernel K n) where
  isProbabilityMeasure := by
    have := Kernel.IsMarkovKernel.map K (measurable_inr : Measurable (Sum.inr : Ω → Slot Ω))
    intro st
    cases st with
    | inl j => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (Sum.inl () : Slot Ω)))
    | inr v => exact inferInstanceAs (IsProbabilityMeasure ((K.map Sum.inr) v.2))

/-- The setting is selected by the actual complete-record state before its
outcome is drawn. The inactive kernel is the same fixed Dirac law for all inputs. -/
def stoppedKernel (R : RawRules Z S Ω) (K : Kernel S Ω) (n : ℕ) :
    Kernel (History Z Ω n) (Slot Ω) := (stateKernel K n).comap (state R n) (state_measurable R n)

instance stoppedKernel_markov (R : RawRules Z S Ω) (K : Kernel S Ω) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (stoppedKernel R K n) := by
  unfold stoppedKernel
  infer_instance

theorem stoppedKernel_apply (R : RawRules Z S Ω) (K : Kernel S Ω) (n : ℕ) (h : History Z Ω n) :
    stoppedKernel R K n h = match state R n h with
      | Sum.inl _ => Measure.dirac (Sum.inl ())
      | Sum.inr (_, s) => (K s).map Sum.inr := by
  simp only [stoppedKernel, Kernel.comap_apply, stateKernel]
  cases state R n h with
  | inl j => rfl
  | inr v => exact Kernel.map_apply _ measurable_inr _

def stoppedLaw (R : RawRules Z S Ω) (seed : Measure Z) (K : Kernel S Ω) [IsMarkovKernel K] :
    Measure (Sample Z (Slot Ω)) := executionLaw seed (stoppedKernel R K)

instance stoppedLaw_probability (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] : IsProbabilityMeasure (stoppedLaw R seed K) := by
  unfold stoppedLaw
  infer_instance

theorem stoppedLaw_prefix (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] (n : ℕ) :
    (stoppedLaw R seed K).map (rawPrefix n) = prefixLaw seed (stoppedKernel R K) n :=
  executionLaw_prefix seed (stoppedKernel R K) n

end LocalCertification.Protocol.MeasurableExecution
