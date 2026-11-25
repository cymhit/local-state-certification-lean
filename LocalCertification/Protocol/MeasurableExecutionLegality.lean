import LocalCertification.Protocol.MeasurableExecutionStopping

/-! All legal paths, deterministic caps, and retention of complete settings and
outcomes. The original seed and every null/impossible outcome path are retained. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open LocalCertification.Information.KernelHistory
open scoped ENNReal Classical
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u
variable {Z S Ω : Type u} [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]

def SlotPresent (o : Slot Ω) : Prop := ∃ x : Ω, o = Sum.inr x

theorem slotPresent_measurable : MeasurableSet {o : Slot Ω | SlotPresent o} := by
  convert (measurableSet_range_inr : MeasurableSet (Set.range (Sum.inr : Ω → Slot Ω))) using 1
  ext o
  simp only [SlotPresent, Set.mem_ofPred_eq, Set.mem_range, eq_comm]

def SlotLegal (R : RawRules Z S Ω) (n : ℕ) (h : History Z Ω n) (o : Slot Ω) : Prop :=
  SlotPresent o ↔ h ∈ active R n

theorem slotLegal_measurable (R : RawRules Z S Ω) (n : ℕ) :
    MeasurableSet {p : History Z Ω n × Slot Ω | SlotLegal R n p.1 p.2} :=
  (measurable_snd slotPresent_measurable).iff (measurable_fst (active_measurable R n))

/-- Legality is pointwise, without reference to a seed law or any input state. -/
def Legal (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) : Prop :=
  ∀ n, SlotLegal R n (rawPrefix n p) (p.2 n)

theorem legal_measurable (R : RawRules Z S Ω) : MeasurableSet {p | Legal R p} := by
  change MeasurableSet {p : Sample Z (Slot Ω) | ∀ n, SlotLegal R n (rawPrefix n p) (p.2 n)}
  convert MeasurableSet.iInter (fun n =>
    ((rawPrefix_measurable n).prodMk ((measurable_pi_apply n).comp measurable_snd))
      (slotLegal_measurable R n)) using 1
  ext p
  simp

theorem stoppedKernel_ae_legal (R : RawRules Z S Ω) (K : Kernel S Ω) [IsMarkovKernel K]
    (n : ℕ) (h : History Z Ω n) :
    ∀ᵐ o ∂stoppedKernel R K n h, SlotLegal R n h o := by
  have hm : MeasurableSet {o : Slot Ω | SlotLegal R n h o} :=
    (measurable_const.prodMk measurable_id) (slotLegal_measurable R n)
  rw [stoppedKernel_apply]
  cases hs : state R n h with
  | inl j =>
    apply (ae_dirac_iff hm).mpr
    simp [SlotLegal, SlotPresent, active, hs]
  | inr v =>
    apply (ae_map_iff measurable_inr.aemeasurable hm).mpr
    exact Filter.Eventually.of_forall (fun x =>
      ⟨fun _ => ⟨v, hs⟩, fun _ => ⟨x, rfl⟩⟩)

/-- The actual trajectory satisfies all legality conditions simultaneously;
this does not alter or quotient the full pointwise legal path set. -/
theorem stoppedLaw_ae_legal (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] : ∀ᵐ p ∂stoppedLaw R seed K, Legal R p := by
  change ∀ᵐ p ∂stoppedLaw R seed K, ∀ n, SlotLegal R n (rawPrefix n p) (p.2 n)
  rw [ae_all_iff]
  intro n
  have h : ∀ᵐ h ∂prefixLaw seed (stoppedKernel R K) (n+1), SlotLegal R n h.1 h.2 :=
    Measure.ae_compProd_of_ae_ae (slotLegal_measurable R n)
      (Filter.Eventually.of_forall (stoppedKernel_ae_legal R K n))
  rw [← stoppedLaw_prefix R seed K (n+1)] at h
  exact (ae_map_iff (rawPrefix_measurable (n+1)).aemeasurable (slotLegal_measurable R n)).mp h

/-- A cap bounds every legal path, including null seeds and zero-probability
outcomes. It is deliberately not an essential supremum. -/
def Capped (R : RawRules Z S Ω) (N : ℕ) : Prop :=
  ∀ p : Sample Z (Slot Ω), Legal R p → stoppingTime R p ≤ (N : ℕ∞)

def Terminates (R : RawRules Z S Ω) (seed : Measure Z) (K : Kernel S Ω) [IsMarkovKernel K] : Prop :=
  ∀ᵐ p ∂stoppedLaw R seed K, stoppingTime R p ≠ ⊤

theorem capped_terminates (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] (N : ℕ) (hcap : Capped R N) : Terminates R seed K := by
  filter_upwards [stoppedLaw_ae_legal R seed K] with p hp
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top N) (hcap p hp)

theorem cost_le_of_capped (R : RawRules Z S Ω) (N : ℕ) (hcap : Capped R N)
    (p : Sample Z (Slot Ω)) (hp : Legal R p) : cost R p ≤ (N : ℝ≥0∞) := by
  simpa only [cost, ENat.toENNReal_coe] using ENat.toENNReal_mono (hcap p hp)

theorem capped_expected_cost (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] (N : ℕ) (hcap : Capped R N) :
    (∫⁻ p, cost R p ∂stoppedLaw R seed K) ≤ (N : ℝ≥0∞) := by
  have h : (∫⁻ p, cost R p ∂stoppedLaw R seed K) ≤
      ∫⁻ _p, (N : ℝ≥0∞) ∂stoppedLaw R seed K := by
    apply lintegral_mono_ae
    filter_upwards [stoppedLaw_ae_legal R seed K] with p hp
    exact cost_le_of_capped R N hcap p hp
  simpa only [lintegral_const, measure_univ, mul_one] using h

def labelSlot {n : ℕ} : State S Ω n × Slot Ω → Unit ⊕ (S × Ω)
  | (Sum.inl _, _) => Sum.inl ()
  | (Sum.inr _, Sum.inl _) => Sum.inl ()
  | (Sum.inr (_, s), Sum.inr x) => Sum.inr (s, x)

theorem labelSlot_measurable (n : ℕ) : Measurable (labelSlot (S := S) (Ω := Ω) (n := n)) := by
  let live : ((Fin n → S × Ω) × S) × Slot Ω → Unit ⊕ (S × Ω) :=
    fun p => labelSlot (Sum.inr p.1, p.2)
  have hlive : Measurable live := by
    have ha : Measurable (fun _ : ((Fin n → S × Ω) × S) × Unit =>
        (Sum.inl () : Unit ⊕ (S × Ω))) := measurable_const
    have hb : Measurable (fun p : ((Fin n → S × Ω) × S) × Ω =>
        (Sum.inr (p.1.2, p.2) : Unit ⊕ (S × Ω))) :=
      measurable_inr.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h := ha.sumElim hb
    have ht := h.comp (MeasurableEquiv.prodSumDistrib ((Fin n → S × Ω) × S) Unit Ω).measurable
    convert ht using 1
    funext p
    rcases p with ⟨⟨h, s⟩, e | x⟩ <;> rfl
  have hstop : Measurable (fun _ : Fin 2 × Slot Ω => (Sum.inl () : Unit ⊕ (S × Ω))) := measurable_const
  have h := hstop.sumElim hlive
  have ht := h.comp (MeasurableEquiv.sumProdDistrib (Fin 2) ((Fin n → S × Ω) × S) (Slot Ω)).measurable
  convert ht using 1
  funext p
  rcases p with ⟨j | v, o⟩ <;> rfl

/-- Complete public records retain the original seed, each entire chosen
setting, its actual outcome, and the common empty stopped tail. -/
def fullRecordSample (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) : Sample Z (Unit ⊕ (S × Ω)) :=
  (p.1, fun n => labelSlot (state R n (rawPrefix n p), p.2 n))

theorem fullRecordSample_measurable (R : RawRules Z S Ω) : Measurable (fullRecordSample R) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr (fun n => (labelSlot_measurable n).comp
    (((state_measurable R n).comp (rawPrefix_measurable n)).prodMk
      ((measurable_pi_apply n).comp measurable_snd))))

theorem fullRecordSample_seed (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) :
    (fullRecordSample R p).1 = p.1 := rfl

theorem fullRecordSample_live (R : RawRules Z S Ω) (p : Sample Z (Slot Ω))
    (n : ℕ) (h : Fin n → S × Ω) (s : S) (x : Ω)
    (hs : state R n (rawPrefix n p) = Sum.inr (h, s)) (hx : p.2 n = Sum.inr x) :
    (fullRecordSample R p).2 n = Sum.inr (s, x) := by
  simp only [fullRecordSample, hs, hx]
  rfl

theorem labelSlot_recovers (R : RawRules Z S Ω) (n : ℕ) (h : History Z Ω n) (o : Slot Ω)
    (hl : SlotLegal R n h o) : Sum.map id Prod.snd (labelSlot (state R n h, o)) = o := by
  cases hs : state R n h with
  | inl j =>
    cases o with
    | inl e => cases e; rfl
    | inr x =>
      obtain ⟨v, hv⟩ := hl.mp ⟨x, rfl⟩
      rw [hs] at hv
      cases hv
  | inr v =>
    cases o with
    | inl e =>
      obtain ⟨x, hx⟩ := hl.mpr ⟨v, hs⟩
      cases hx
    | inr x => rfl

/-- Forgetting setting labels recovers every original legal path exactly,
not merely almost surely. Thus complete public recording loses no information. -/
theorem fullRecordSample_recovers (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) (hp : Legal R p) (n : ℕ) :
    Sum.map id Prod.snd ((fullRecordSample R p).2 n) = p.2 n :=
  labelSlot_recovers R n (rawPrefix n p) (p.2 n) (hp n)

def fullPrefix (R : RawRules Z S Ω) : ∀ n, History Z Ω n → FullHistory Z (Unit ⊕ (S × Ω)) n
  | 0 => id
  | n+1 => fun h => (fullPrefix R n h.1, labelSlot (state R n h.1, h.2))

theorem fullPrefix_measurable (R : RawRules Z S Ω) (n : ℕ) : Measurable (fullPrefix R n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact (ih.comp measurable_fst).prodMk ((labelSlot_measurable n).comp
      (((state_measurable R n).comp measurable_fst).prodMk measurable_snd))

theorem fullPrefix_rawPrefix (R : RawRules Z S Ω) (n : ℕ) (p : Sample Z (Slot Ω)) :
    fullPrefix R n (rawPrefix n p) = rawPrefix n (fullRecordSample R p) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun h => (h, (fullRecordSample R p).2 n)) ih

def fullRecordLaw (R : RawRules Z S Ω) (seed : Measure Z) (K : Kernel S Ω) [IsMarkovKernel K] :
    Measure (Sample Z (Unit ⊕ (S × Ω))) := (stoppedLaw R seed K).map (fullRecordSample R)

theorem fullRecordLaw_prefix (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] (n : ℕ) :
    (fullRecordLaw R seed K).map (rawPrefix n) =
      (prefixLaw seed (stoppedKernel R K) n).map (fullPrefix R n) := by
  rw [fullRecordLaw, Measure.map_map (rawPrefix_measurable n) (fullRecordSample_measurable R),
    ← stoppedLaw_prefix R seed K n, Measure.map_map (fullPrefix_measurable R n) (rawPrefix_measurable n)]
  congr 1
  funext p
  exact (fullPrefix_rawPrefix R n p).symm

theorem legal_execution_and_full_records (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] :
    (∀ᵐ p ∂stoppedLaw R seed K, Legal R p) ∧
    (∀ N : ℕ, Capped R N → Terminates R seed K ∧
      (∫⁻ p, cost R p ∂stoppedLaw R seed K) ≤ (N : ℝ≥0∞)) ∧
    (∃ F : Sample Z (Slot Ω) → Sample Z (Unit ⊕ (S × Ω)), Measurable F ∧
      (∀ p, (F p).1 = p.1) ∧
      (∀ p (n : ℕ) (h : Fin n → S × Ω) (s : S) (x : Ω),
        state R n (rawPrefix n p) = Sum.inr (h, s) → p.2 n = Sum.inr x →
        (F p).2 n = Sum.inr (s, x)) ∧
      (∀ p, Legal R p → ∀ n, Sum.map id Prod.snd ((F p).2 n) = p.2 n)) :=
  ⟨stoppedLaw_ae_legal R seed K, fun N h => ⟨capped_terminates R seed K N h, capped_expected_cost R seed K N h⟩,
    fullRecordSample R, fullRecordSample_measurable R, fullRecordSample_seed R,
    fullRecordSample_live R, fullRecordSample_recovers R⟩

end LocalCertification.Protocol.MeasurableExecution
