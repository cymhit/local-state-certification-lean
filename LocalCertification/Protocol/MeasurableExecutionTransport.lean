import LocalCertification.Protocol.MeasurableExecutionBorn
import LocalCertification.Protocol.MeasurableExecutionUniqueness
import LocalCertification.Quantum.MeasurablePOVMMap

/-! Representation changes preserve the actual executor, including every raw
path and null branch. The measurable equivalences may cross universes. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open LocalCertification.Information.KernelHistory
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.Transport
universe u v w
variable {Z S Ω : Type u} {Z' S' Ω' : Type v}
  [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]
  [MeasurableSpace Z'] [MeasurableSpace S'] [MeasurableSpace Ω']

def slotEquiv (e : Ω ≃ᵐ Ω') : Slot Ω ≃ᵐ Slot Ω' :=
  MeasurableEquiv.sumCongr (MeasurableEquiv.refl Unit) e

def sampleEquiv (eZ : Z ≃ᵐ Z') (eΩ : Ω ≃ᵐ Ω') :
    Sample Z (Slot Ω) ≃ᵐ Sample Z' (Slot Ω') where
  toFun p := (eZ p.1, fun n => slotEquiv eΩ (p.2 n))
  invFun p := (eZ.symm p.1, fun n => (slotEquiv eΩ).symm (p.2 n))
  left_inv p := by
    apply Prod.ext (eZ.symm_apply_apply _)
    funext n
    exact (slotEquiv eΩ).symm_apply_apply _
  right_inv p := by
    apply Prod.ext (eZ.apply_symm_apply _)
    funext n
    exact (slotEquiv eΩ).apply_symm_apply _
  measurable_toFun := (eZ.measurable.comp measurable_fst).prodMk
    (measurable_pi_iff.mpr (fun n => (slotEquiv eΩ).measurable.comp
      ((measurable_pi_apply n).comp measurable_snd)))
  measurable_invFun := (eZ.symm.measurable.comp measurable_fst).prodMk
    (measurable_pi_iff.mpr (fun n => (slotEquiv eΩ).symm.measurable.comp
      ((measurable_pi_apply n).comp measurable_snd)))

def historyEquiv (eZ : Z ≃ᵐ Z') (eΩ : Ω ≃ᵐ Ω') :
    ∀ n, History Z Ω n ≃ᵐ History Z' Ω' n
  | 0 => eZ
  | n+1 => (historyEquiv eZ eΩ n).prodCongr (slotEquiv eΩ)

theorem historyEquiv_seed (eZ : Z ≃ᵐ Z') (eΩ : Ω ≃ᵐ Ω') (n : ℕ) (h : History Z Ω n) :
    historySeed n (historyEquiv eZ eΩ n h) = eZ (historySeed n h) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih h.1

theorem historyEquiv_prefix (eZ : Z ≃ᵐ Z') (eΩ : Ω ≃ᵐ Ω')
    (n : ℕ) (p : Sample Z (Slot Ω)) :
    rawPrefix n (sampleEquiv eZ eΩ p) = historyEquiv eZ eΩ n (rawPrefix n p) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun h => (h, slotEquiv eΩ (p.2 n))) ih

def recordsMap (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω') {n : ℕ} (h : Fin n → S × Ω) :
    Fin n → S' × Ω' := fun i => (eS (h i).1, eΩ (h i).2)

theorem recordsMap_inverse (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω') {n : ℕ} (h : Fin n → S × Ω) :
    recordsMap eS.symm eΩ.symm (recordsMap eS eΩ h) = h := by
  funext i
  simp [recordsMap]

theorem recordsMap_snoc (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω') {n : ℕ}
    (h : Fin n → S × Ω) (s : S) (x : Ω) :
    recordsMap eS eΩ (Fin.snoc h (s, x)) = Fin.snoc (recordsMap eS eΩ h) (eS s, eΩ x) := by
  funext i
  cases i using Fin.lastCases <;> simp [recordsMap]

def rules (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω') (R : RawRules Z S Ω) :
    RawRules Z' S' Ω' where
  rule n p := Sum.map id eS (R.rule n (eZ.symm p.1, recordsMap eS.symm eΩ.symm p.2))
  measurable_rule n := by
    apply (measurable_id.sumMap eS.measurable).comp
    apply (R.measurable_rule n).comp
    apply (eZ.symm.measurable.comp measurable_fst).prodMk
    apply measurable_pi_iff.mpr
    intro i
    exact (eS.symm.measurable.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))).prodMk
      (eΩ.symm.measurable.comp (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)))

def stateMap (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω') {n : ℕ} : State S Ω n → State S' Ω' n :=
  Sum.map id (fun v => (recordsMap eS eΩ v.1, eS v.2))

theorem stateMap_withAction (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω') {n : ℕ}
    (h : Fin n → S × Ω) (a : Action S) :
    stateMap eS eΩ (withAction h a) = withAction (recordsMap eS eΩ h) (Sum.map id eS a) := by
  cases a <;> rfl

theorem advance_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) {n : ℕ} (z : Z) (st : State S Ω n) (o : Slot Ω) :
    advance (rules eZ eS eΩ R) (eZ z) (stateMap eS eΩ st) (slotEquiv eΩ o) =
      stateMap eS eΩ (advance R z st o) := by
  rcases st with j | ⟨h, s⟩
  · rfl
  rcases o with e | x
  · rfl
  change withAction (Fin.snoc (recordsMap eS eΩ h) (eS s, eΩ x))
    ((rules eZ eS eΩ R).rule (n+1) (eZ z, Fin.snoc (recordsMap eS eΩ h) (eS s, eΩ x))) =
    stateMap eS eΩ (withAction (Fin.snoc h (s, x)) (R.rule (n+1) (z, Fin.snoc h (s, x))))
  rw [stateMap_withAction, ← recordsMap_snoc]
  congr 1
  change Sum.map id eS (R.rule (n+1)
    (eZ.symm (eZ z), recordsMap eS.symm eΩ.symm (recordsMap eS eΩ (Fin.snoc h (s, x))))) = _
  rw [eZ.symm_apply_apply, recordsMap_inverse]

theorem state_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (n : ℕ) (h : History Z Ω n) :
    state (rules eZ eS eΩ R) n (historyEquiv eZ eΩ n h) = stateMap eS eΩ (state R n h) := by
  induction n with
  | zero =>
    change Z at h
    change withAction Fin.elim0 _ = stateMap eS eΩ (withAction Fin.elim0 _)
    rw [stateMap_withAction]
    have he : recordsMap eS eΩ (Fin.elim0 : Fin 0 → S × Ω) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    have hi : recordsMap eS.symm eΩ.symm (Fin.elim0 : Fin 0 → S' × Ω') = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    change withAction Fin.elim0 (Sum.map id eS (R.rule 0
      (eZ.symm (eZ h), recordsMap eS.symm eΩ.symm Fin.elim0))) =
      withAction (recordsMap eS eΩ Fin.elim0) (Sum.map id eS (R.rule 0 (h, Fin.elim0)))
    rw [eZ.symm_apply_apply, he, hi]
  | succ n ih =>
    change advance _ (historySeed n (historyEquiv eZ eΩ n h.1))
      (state _ n (historyEquiv eZ eΩ n h.1)) (slotEquiv eΩ h.2) = _
    rw [historyEquiv_seed, ih]
    exact advance_conjugacy eZ eS eΩ R _ _ _

theorem active_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (n : ℕ) (h : History Z Ω n) :
    historyEquiv eZ eΩ n h ∈ active (rules eZ eS eΩ R) n ↔ h ∈ active R n := by
  simp only [active, mem_ofPred_eq, state_conjugacy]
  cases state R n h <;> simp [stateMap]

theorem pathActive_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) (n : ℕ) :
    PathActive (rules eZ eS eΩ R) (sampleEquiv eZ eΩ p) n ↔ PathActive R p n := by
  change rawPrefix n (sampleEquiv eZ eΩ p) ∈ active (rules eZ eS eΩ R) n ↔
    rawPrefix n p ∈ active R n
  rw [historyEquiv_prefix, active_conjugacy]

theorem stoppingTime_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) :
    stoppingTime (rules eZ eS eΩ R) (sampleEquiv eZ eΩ p) = stoppingTime R p := by
  apply le_antisymm
  · cases ht : stoppingTime R p with
    | top => exact le_top
    | coe m =>
      apply (stoppingTime_le_iff _ _ m).mpr
      rw [pathActive_conjugacy]
      exact (stoppingTime_le_iff R p m).mp ht.le
  · cases ht : stoppingTime (rules eZ eS eΩ R) (sampleEquiv eZ eΩ p) with
    | top => exact le_top
    | coe m =>
      apply (stoppingTime_le_iff _ _ m).mpr
      rw [← pathActive_conjugacy eZ eS eΩ]
      exact (stoppingTime_le_iff _ _ m).mp ht.le

theorem decision_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) :
    terminalDecision (rules eZ eS eΩ R) (sampleEquiv eZ eΩ p) = terminalDecision R p := by
  cases ht : stoppingTime R p with
  | top => rw [terminalDecision_of_top R p ht, terminalDecision_of_top _ _
      ((stoppingTime_conjugacy eZ eS eΩ R p).trans ht)]
  | coe m =>
    rw [terminalDecision_of_stopped R p m ht.le, terminalDecision_of_stopped _ _ m
      ((stoppingTime_conjugacy eZ eS eΩ R p).trans ht).le, historyEquiv_prefix, state_conjugacy]
    cases state R m (rawPrefix m p) <;> rfl

theorem legal_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) :
    Legal (rules eZ eS eΩ R) (sampleEquiv eZ eΩ p) ↔ Legal R p := by
  unfold Legal SlotLegal
  simp only [historyEquiv_prefix, active_conjugacy]
  apply forall_congr'
  intro n
  have hs : SlotPresent ((sampleEquiv eZ eΩ p).2 n) ↔ SlotPresent (p.2 n) := by
    change SlotPresent (slotEquiv eΩ (p.2 n)) ↔ SlotPresent (p.2 n)
    cases p.2 n with
    | inl e =>
      change (∃ x : Ω', (Sum.inl e : Slot Ω') = Sum.inr x) ↔
        (∃ x : Ω, (Sum.inl e : Slot Ω) = Sum.inr x)
      simp
    | inr x => exact ⟨fun _ => ⟨x, rfl⟩, fun _ => ⟨eΩ x, rfl⟩⟩
  rw [hs]

theorem capped_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (N : ℕ) : Capped (rules eZ eS eΩ R) N ↔ Capped R N := by
  constructor
  · intro h p hp
    rw [← stoppingTime_conjugacy eZ eS eΩ]
    exact h _ ((legal_conjugacy eZ eS eΩ R p).mpr hp)
  · intro h p hp
    obtain ⟨q, rfl⟩ := (sampleEquiv eZ eΩ).surjective p
    rw [stoppingTime_conjugacy]
    exact h q ((legal_conjugacy eZ eS eΩ R q).mp hp)

def kernel (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω') (K : Kernel S Ω) : Kernel S' Ω' :=
  (K.map eΩ).comap eS.symm eS.symm.measurable

instance kernel_markov (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω') (K : Kernel S Ω) [IsMarkovKernel K] :
    IsMarkovKernel (kernel eS eΩ K) := by
  have := Kernel.IsMarkovKernel.map K eΩ.measurable
  unfold kernel
  infer_instance

theorem kernel_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (K : Kernel S Ω) (n : ℕ) (h : History Z Ω n) :
    (stoppedKernel R K n h).map (slotEquiv eΩ) =
      stoppedKernel (rules eZ eS eΩ R) (kernel eS eΩ K) n (historyEquiv eZ eΩ n h) := by
  rw [stoppedKernel_apply, stoppedKernel_apply, state_conjugacy]
  cases hs : state R n h with
  | inl j =>
    rw [Measure.map_dirac' (slotEquiv eΩ).measurable]
    rfl
  | inr v =>
    change ((K v.2).map Sum.inr).map (slotEquiv eΩ) = ((kernel eS eΩ K) (eS v.2)).map Sum.inr
    rw [kernel, Kernel.comap_apply, Kernel.map_apply _ eΩ.measurable, eS.symm_apply_apply,
      Measure.map_map (slotEquiv eΩ).measurable measurable_inr,
      Measure.map_map measurable_inr eΩ.measurable]
    rfl

private theorem map_compProd_conjugacy {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (η : Kernel C D) [IsSFiniteKernel η] (f : A → C) (g : B → D)
    (hf : Measurable f) (hg : Measurable g) (hκ : ∀ a, (κ a).map g = η (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f g) = μ.map f ⊗ₘ η := by
  ext E hE
  rw [Measure.map_apply (hf.prodMap hg) hE, Measure.compProd_apply ((hf.prodMap hg) hE),
    Measure.compProd_apply hE, lintegral_map (Kernel.measurable_kernel_prodMk_left hE) hf]
  apply lintegral_congr
  intro a
  rw [← hκ a, Measure.map_apply hg (measurable_prodMk_left hE)]
  rfl

theorem prefixLaw_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] (n : ℕ) :
    (prefixLaw seed (stoppedKernel R K) n).map (historyEquiv eZ eΩ n) =
      prefixLaw (seed.map eZ) (stoppedKernel (rules eZ eS eΩ R) (kernel eS eΩ K)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (prefixLaw seed (stoppedKernel R K) n ⊗ₘ stoppedKernel R K n).map
      (Prod.map (historyEquiv eZ eΩ n) (slotEquiv eΩ)) = _
    rw [map_compProd_conjugacy _ _ (stoppedKernel (rules eZ eS eΩ R) (kernel eS eΩ K) n)
      _ _ (historyEquiv eZ eΩ n).measurable (slotEquiv eΩ).measurable
      (kernel_conjugacy eZ eS eΩ R K n), ih]
    rfl

theorem stoppedLaw_conjugacy (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] :
    stoppedLaw (rules eZ eS eΩ R) (seed.map eZ) (kernel eS eΩ K) =
      (stoppedLaw R seed K).map (sampleEquiv eZ eΩ) := by
  let : IsProbabilityMeasure (seed.map eZ) := by
    constructor
    rw [Measure.map_apply eZ.measurable MeasurableSet.univ]
    simp
  let : IsProbabilityMeasure ((stoppedLaw R seed K).map (sampleEquiv eZ eΩ)) := by
    constructor
    rw [Measure.map_apply (sampleEquiv eZ eΩ).measurable MeasurableSet.univ]
    simp
  apply law_ext_prefix
  intro n
  rw [stoppedLaw_prefix]
  symm
  calc
    ((stoppedLaw R seed K).map (sampleEquiv eZ eΩ)).map (rawPrefix n) =
        (stoppedLaw R seed K).map (historyEquiv eZ eΩ n ∘ rawPrefix n) := by
      rw [Measure.map_map (rawPrefix_measurable n) (sampleEquiv eZ eΩ).measurable]
      congr 1
      funext p
      exact historyEquiv_prefix eZ eΩ n p
    _ = ((stoppedLaw R seed K).map (rawPrefix n)).map (historyEquiv eZ eΩ n) := by
      rw [Measure.map_map (historyEquiv eZ eΩ n).measurable (rawPrefix_measurable n)]
    _ = _ := by
      rw [stoppedLaw_prefix]
      exact prefixLaw_conjugacy eZ eS eΩ R seed K n

variable {I : Type w} [Fintype I] [DecidableEq I]

def bornProtocol (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) : BornProtocol Z' S' Ω' I where
  toRawRules := rules eZ eS eΩ P.toRawRules
  seedLaw := P.seedLaw.map eZ
  seed_probability := by
    constructor
    rw [Measure.map_apply eZ.measurable MeasurableSet.univ]
    simp
  measurements := (P.measurements.map eΩ eΩ.measurable).reindex eS.symm eS.symm.measurable

theorem bornProtocol_kernel (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (ρ : QIT.State I) :
    (bornProtocol eZ eS eΩ P).measurements.bornKernel ρ = kernel eS eΩ (P.measurements.bornKernel ρ) := by
  ext1 s
  rw [kernel, Kernel.comap_apply, Kernel.map_apply _ eΩ.measurable]
  exact (P.measurements.measurement (eS.symm s)).born_map eΩ eΩ.measurable ρ

theorem bornProtocol_law (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (ρ : QIT.State I) :
    (bornProtocol eZ eS eΩ P).law ρ = (P.law ρ).map (sampleEquiv eZ eΩ) := by
  change stoppedLaw (rules eZ eS eΩ P.toRawRules) (P.seedLaw.map eZ)
    ((bornProtocol eZ eS eΩ P).measurements.bornKernel ρ) = _
  simp only [bornProtocol_kernel]
  exact stoppedLaw_conjugacy eZ eS eΩ P.toRawRules P.seedLaw (P.measurements.bornKernel ρ)

theorem bornProtocol_time (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (p : Sample Z (Slot Ω)) :
    (bornProtocol eZ eS eΩ P).time (sampleEquiv eZ eΩ p) = P.time p :=
  stoppingTime_conjugacy eZ eS eΩ P.toRawRules p

theorem bornProtocol_decision (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (p : Sample Z (Slot Ω)) :
    (bornProtocol eZ eS eΩ P).reportedDecision (sampleEquiv eZ eΩ p) = P.reportedDecision p :=
  decision_conjugacy eZ eS eΩ P.toRawRules p

theorem bornProtocol_expectedCopies (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (ρ : QIT.State I) :
    (bornProtocol eZ eS eΩ P).expectedCopies ρ = P.expectedCopies ρ := by
  change (∫⁻ p, (bornProtocol eZ eS eΩ P).copyCost p ∂(bornProtocol eZ eS eΩ P).law ρ) =
    ∫⁻ p, P.copyCost p ∂P.law ρ
  rw [bornProtocol_law,
    lintegral_map (bornProtocol eZ eS eΩ P).copyCost_measurable (sampleEquiv eZ eΩ).measurable]
  apply lintegral_congr
  intro p
  exact congrArg ENat.toENNReal (bornProtocol_time eZ eS eΩ P p)

theorem bornProtocol_terminates_iff (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (ρ : QIT.State I) :
    (bornProtocol eZ eS eΩ P).Terminates ρ ↔ P.Terminates ρ := by
  unfold BornProtocol.Terminates
  rw [bornProtocol_law]
  have hm : MeasurableSet {p | (bornProtocol eZ eS eΩ P).time p ≠ ⊤} :=
    ((bornProtocol eZ eS eΩ P).time_measurable (measurableSet_singleton ⊤)).compl
  rw [ae_map_iff (sampleEquiv eZ eΩ).measurable.aemeasurable hm]
  simp only [bornProtocol_time]

theorem bornProtocol_decision_measure (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (ρ : QIT.State I) (j : Fin 2) :
    (bornProtocol eZ eS eΩ P).law ρ {p | (bornProtocol eZ eS eΩ P).reportedDecision p = j} =
      P.law ρ {p | P.reportedDecision p = j} := by
  have hm : MeasurableSet {p | (bornProtocol eZ eS eΩ P).reportedDecision p = j} :=
    (bornProtocol eZ eS eΩ P).reportedDecision_measurable (measurableSet_singleton j)
  rw [bornProtocol_law, Measure.map_apply (sampleEquiv eZ eΩ).measurable hm]
  congr 1
  ext p
  exact congrArg (fun d => d = j) (bornProtocol_decision eZ eS eΩ P p) |> Iff.of_eq

theorem bornProtocol_valid_iff (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (ψ : QIT.PureVector I) (a b δ : ℝ) :
    (bornProtocol eZ eS eΩ P).Valid ψ a b δ ↔ P.Valid ψ a b δ := by
  unfold BornProtocol.Valid
  simp only [bornProtocol_terminates_iff, bornProtocol_decision_measure]

theorem bornProtocol_capped_iff (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) (N : ℕ) :
    (bornProtocol eZ eS eΩ P).Capped N ↔ P.Capped N :=
  capped_conjugacy eZ eS eΩ P.toRawRules N

end LocalCertification.Protocol.MeasurableExecution.Transport

namespace LocalCertification.Protocol.MeasurableExecution
universe u v w
variable {Z S Ω : Type u} {Z' S' Ω' : Type v} {I : Type w}
  [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]
  [MeasurableSpace Z'] [MeasurableSpace S'] [MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]

/-- The original rules, measurements and entire physical experiment are
preserved under a change of measurable representation, including universes. -/
theorem exists_transport_execution (eZ : Z ≃ᵐ Z') (eS : S ≃ᵐ S') (eΩ : Ω ≃ᵐ Ω')
    (P : BornProtocol Z S Ω I) :
    ∃ Q : BornProtocol Z' S' Ω' I,
      Q.seedLaw = P.seedLaw.map eZ ∧
      (∀ m z h, Q.rule m (z, h) = Sum.map id eS
        (P.rule m (eZ.symm z, fun i => (eS.symm (h i).1, eΩ.symm (h i).2)))) ∧
      (∀ s, Q.measurements.measurement s =
        (P.measurements.measurement (eS.symm s)).map eΩ eΩ.measurable) ∧
      (∀ ρ, Q.law ρ = (P.law ρ).map
        (fun p => (eZ p.1, fun m => Sum.map id eΩ (p.2 m)))) ∧
      (∀ p, Q.time (eZ p.1, fun m => Sum.map id eΩ (p.2 m)) = P.time p) ∧
      (∀ p, Q.reportedDecision (eZ p.1, fun m => Sum.map id eΩ (p.2 m)) = P.reportedDecision p) ∧
      (∀ p, Legal Q.toRawRules (eZ p.1, fun m => Sum.map id eΩ (p.2 m)) ↔ Legal P.toRawRules p) ∧
      (∀ ρ, Q.expectedCopies ρ = P.expectedCopies ρ) ∧
      (∀ ψ a b δ, Q.Valid ψ a b δ ↔ P.Valid ψ a b δ) ∧
      (∀ N, Q.Capped N ↔ P.Capped N) :=
  ⟨Transport.bornProtocol eZ eS eΩ P, rfl, fun _ _ _ => rfl, fun _ => rfl,
    Transport.bornProtocol_law eZ eS eΩ P, Transport.bornProtocol_time eZ eS eΩ P,
    Transport.bornProtocol_decision eZ eS eΩ P, Transport.legal_conjugacy eZ eS eΩ P.toRawRules,
    Transport.bornProtocol_expectedCopies eZ eS eΩ P, Transport.bornProtocol_valid_iff eZ eS eΩ P,
    Transport.bornProtocol_capped_iff eZ eS eΩ P⟩

end LocalCertification.Protocol.MeasurableExecution
