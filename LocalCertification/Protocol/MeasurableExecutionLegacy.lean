import LocalCertification.Protocol.MeasurableExecutionFiltration
import LocalCertification.Protocol.LegalStopping

/-! Exact representation bridge from the existing finite-alphabet executor.
Finiteness is used only to compare its scoped Option sigma algebra with the
ordinary sum sigma algebra; it is not a restriction on the general executor. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.Legacy
universe u
variable {Z S Ω : Type u} [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]
  [Inhabited S] [Inhabited Ω] [Fintype Ω] [MeasurableSingletonClass Ω]

def fromOption : Option Ω → Slot Ω
  | none => Sum.inl ()
  | some x => Sum.inr x

def toOption : Slot Ω → Option Ω
  | Sum.inl _ => none
  | Sum.inr x => some x

omit [Inhabited Ω] [MeasurableSingletonClass Ω] in
theorem fromOption_measurable : Measurable (fromOption (Ω := Ω)) := measurable_of_countable _
omit [Inhabited Ω] in
theorem toOption_measurable : Measurable (toOption (Ω := Ω)) :=
  measurable_const.sumElim (measurable_of_countable Option.some)

def sampleEquiv : RawSample Z Ω ≃ᵐ Sample Z (Slot Ω) where
  toFun p := (p.1, fun n => fromOption (p.2 n))
  invFun p := (p.1, fun n => toOption (p.2 n))
  left_inv p := by
    apply Prod.ext
    · rfl
    funext n
    change toOption (fromOption (p.2 n)) = p.2 n
    cases p.2 n <;> rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    funext n
    change fromOption (toOption (p.2 n)) = p.2 n
    cases p.2 n with
    | inl e => cases e; rfl
    | inr x => rfl
  measurable_toFun := measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun n => fromOption_measurable.comp ((measurable_pi_apply n).comp measurable_snd)))
  measurable_invFun := measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun n => toOption_measurable.comp ((measurable_pi_apply n).comp measurable_snd)))

def toHistory : ∀ m, LocalCertification.Information.SlotHistory Z Ω m → History Z Ω m
  | 0 => ULift.down
  | m+1 => fun h => (toHistory m h.1, fromOption h.2)

def fromHistory : ∀ m, History Z Ω m → LocalCertification.Information.SlotHistory Z Ω m
  | 0 => ULift.up
  | m+1 => fun h => (fromHistory m h.1, toOption h.2)

omit [Inhabited Ω] in
theorem fromHistory_measurable (m : ℕ) : Measurable (fromHistory (Z := Z) (Ω := Ω) m) := by
  induction m with
  | zero => exact measurable_up
  | succ m ih => exact (ih.comp measurable_fst).prodMk (toOption_measurable.comp measurable_snd)

omit [MeasurableSpace Z] [MeasurableSpace Ω] [Inhabited Ω] [Fintype Ω] [MeasurableSingletonClass Ω] in
theorem fromHistory_toHistory (m : ℕ) (h : LocalCertification.Information.SlotHistory Z Ω m) :
    fromHistory m (toHistory m h) = h := by
  induction m with
  | zero => rfl
  | succ m ih =>
    apply Prod.ext (ih h.1)
    change toOption (fromOption h.2) = h.2
    cases h.2 <;> rfl

omit [Inhabited Ω] in
theorem fromHistory_rawPrefix (m : ℕ) (p : Sample Z (Slot Ω)) :
    fromHistory m (rawPrefix m p) = Protocol.rawPrefix m (sampleEquiv.symm p) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (fun h => (h, toOption (p.2 m))) ih

omit [Inhabited Ω] [MeasurableSingletonClass Ω] in
theorem toHistory_measurable (m : ℕ) : Measurable (toHistory (Z := Z) (Ω := Ω) m) := by
  induction m with
  | zero => exact measurable_down
  | succ m ih => exact (ih.comp measurable_fst).prodMk (fromOption_measurable.comp measurable_snd)

omit [MeasurableSpace Z] [MeasurableSpace Ω] [Inhabited Ω] [Fintype Ω] [MeasurableSingletonClass Ω] in
theorem toHistory_seed (m : ℕ) (h : LocalCertification.Information.SlotHistory Z Ω m) :
    historySeed m (toHistory m h) = Protocol.slotSeed m h := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih h.1

omit [Inhabited Ω] in
theorem toHistory_rawPrefix (m : ℕ) (p : RawSample Z Ω) :
    toHistory m (Protocol.rawPrefix m p) = rawPrefix m (sampleEquiv p) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (fun h => (h, fromOption (p.2 m))) ih

def collapseState {m : ℕ} (st : ExecutionState S Ω m) : State S Ω m :=
  withAction (fun i => paddedRecordValue (st.1 i)) st.2

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
theorem collapse_advance (R : RawRules Z S Ω) (m : ℕ) (z : Z)
    (st : ExecutionState S Ω m) (o : Option Ω) :
    advance R z (collapseState st) (fromOption o) = collapseState (Protocol.advance R z st o) := by
  rcases st with ⟨h, j | s⟩
  · simp [collapseState, withAction, advance, Protocol.advance, actionContinues, appendEmpty]
  · cases o with
    | none => rfl
    | some x =>
      have he : (fun i : Fin (m+1) => paddedRecordValue
          ((Fin.snoc (α := fun _ : Fin (m+1) => PaddedRecord S Ω) h (Sum.inr (s, x))) i)) =
          Fin.snoc (α := fun _ : Fin (m+1) => S × Ω) (fun i => paddedRecordValue (h i)) (s, x) := by
        funext i
        cases i using Fin.lastCases <;> simp [paddedRecordValue]
      simp only [collapseState, withAction, fromOption, advance, Protocol.advance,
        actionContinues, Sum.elim_inr, ite_true, appendOutcome, actionSetting, id_eq]
      rw [he]

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
/-- Both interpreters compute the same decision or live complete history at
every raw prefix, even inconsistent or null prefixes. -/
theorem state_toHistory (R : RawRules Z S Ω) (m : ℕ)
    (h : LocalCertification.Information.SlotHistory Z Ω m) :
    state R m (toHistory m h) = collapseState (Protocol.execPrefix R m h) := by
  induction m with
  | zero =>
    change withAction _ _ = withAction _ _
    congr 1
    funext i
    exact Fin.elim0 i
  | succ m ih =>
    change advance R (historySeed m (toHistory m h.1)) (state R m (toHistory m h.1)) (fromOption h.2) = _
    rw [toHistory_seed, ih]
    exact collapse_advance R m _ _ _

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
theorem active_toHistory (R : RawRules Z S Ω) (m : ℕ)
    (h : LocalCertification.Information.SlotHistory Z Ω m) :
    toHistory m h ∈ active R m ↔ h ∈ Protocol.activePrefix R m := by
  change (∃ v, state R m (toHistory m h) = Sum.inr v) ↔ _
  rw [state_toHistory]
  cases he : (Protocol.execPrefix R m h).2 with
  | inl j => simp [collapseState, he, withAction, Protocol.activePrefix, actionContinues]
  | inr s => simp [collapseState, he, withAction, Protocol.activePrefix, actionContinues]

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
theorem decision_toHistory (R : RawRules Z S Ω) (m : ℕ)
    (h : LocalCertification.Information.SlotHistory Z Ω m) :
    decision (state R m (toHistory m h)) = actionDecision (Protocol.execPrefix R m h).2 := by
  rw [state_toHistory]
  cases he : (Protocol.execPrefix R m h).2 <;>
    simp only [collapseState, he, withAction, decision, actionDecision, Sum.elim_inl, Sum.elim_inr]

theorem slotLegal_sampleEquiv (R : RawRules Z S Ω) (p : RawSample Z Ω) (m : ℕ) :
    SlotLegal R m (rawPrefix m (sampleEquiv p)) ((sampleEquiv p).2 m) ↔
      (p.2 m ≠ none ↔ Protocol.rawPrefix m p ∈ Protocol.activePrefix R m) := by
  change (SlotPresent (fromOption (p.2 m)) ↔ rawPrefix m (sampleEquiv p) ∈ active R m) ↔ _
  rw [← toHistory_rawPrefix, active_toHistory]
  cases p.2 m <;> simp [SlotPresent, fromOption]

theorem legal_sampleEquiv (R : RawRules Z S Ω) (p : RawSample Z Ω) :
    Legal R (sampleEquiv p) ↔ ∀ m, ConsistentPrefix R m (Protocol.rawPrefix m p) := by
  constructor
  · intro hp m
    induction m with
    | zero => trivial
    | succ m ih => exact ⟨ih, (slotLegal_sampleEquiv R p m).mp (hp m)⟩
  · intro hp m
    exact (slotLegal_sampleEquiv R p m).mpr (hp (m+1)).2

theorem active_sampleEquiv (R : RawRules Z S Ω) (p : RawSample Z Ω)
    (hp : ∀ m, ConsistentPrefix R m (Protocol.rawPrefix m p)) (m : ℕ) :
    PathActive R (sampleEquiv p) m ↔ Protocol.runContinues R p.1 (fun k => (p.2 k).getD default) m := by
  change rawPrefix m (sampleEquiv p) ∈ active R m ↔ _
  rw [← toHistory_rawPrefix, active_toHistory]
  rw [← Protocol.legalPath_logicalPrefix R ⟨p, hp⟩ m]
  rfl

theorem stoppingTime_sampleEquiv (R : RawRules Z S Ω) (p : RawSample Z Ω)
    (hp : ∀ m, ConsistentPrefix R m (Protocol.rawPrefix m p)) :
    stoppingTime R (sampleEquiv p) = Protocol.stoppingTime R p.1 (fun n => (p.2 n).getD default) := by
  have hle (m : ℕ) : stoppingTime R (sampleEquiv p) ≤ (m : ℕ∞) ↔
      Protocol.stoppingTime R p.1 (fun n => (p.2 n).getD default) ≤ (m : WithTop ℕ) := by
    rw [stoppingTime_le_iff, Protocol.stoppingTime_le_iff]
    exact not_congr (active_sampleEquiv R p hp m)
  apply le_antisymm
  · cases ht : Protocol.stoppingTime R p.1 (fun n => (p.2 n).getD default) with
    | top => exact le_top
    | coe m =>
      exact (hle m).mpr (by rw [ht]; exact le_rfl)
  · cases ht : stoppingTime R (sampleEquiv p) with
    | top => exact le_top
    | coe m =>
      exact (hle m).mp (by rw [ht])

theorem terminalDecision_sampleEquiv (R : RawRules Z S Ω) (p : RawSample Z Ω)
    (hp : ∀ m, ConsistentPrefix R m (Protocol.rawPrefix m p)) :
    terminalDecision R (sampleEquiv p) = Protocol.terminalDecision R p.1 (fun n => (p.2 n).getD default) := by
  classical
  by_cases ht : ∃ m, ¬Protocol.runContinues R p.1 (fun n => (p.2 n).getD default) m
  · obtain ⟨m, hm⟩ := ht
    have hnew : stoppingTime R (sampleEquiv p) ≤ (m : ℕ∞) :=
      (stoppingTime_le_iff R _ m).mpr (fun ha => hm ((active_sampleEquiv R p hp m).mp ha))
    rw [terminalDecision_of_stopped R _ m hnew, ← toHistory_rawPrefix, decision_toHistory,
      Protocol.terminalDecision_eq_of_stopped R _ _ m hm]
    rw [← Protocol.legalPath_logicalPrefix R ⟨p, hp⟩ m]
    rfl
  · have hnew : stoppingTime R (sampleEquiv p) = ⊤ := by
      apply (stoppingTime_eq_top_iff R _).mpr
      intro m
      exact (active_sampleEquiv R p hp m).mpr (not_not.mp (not_exists.mp ht m))
    rw [terminalDecision_of_top R _ hnew]
    simp only [Protocol.terminalDecision, dite_eq_right ht]

theorem capped_iff (R : RawRules Z S Ω) (N : ℕ) : Capped R N ↔ EveryPathCap R N := by
  constructor
  · intro hn z x
    have hc (m : ℕ) : ConsistentPrefix R m (Protocol.rawPrefix m (Protocol.logicalRawPath R z x)) := by
      rw [Protocol.logicalRawPath_prefix]
      exact Protocol.logicalPrefix_consistent R z x m
    have ht := hn (sampleEquiv (Protocol.logicalRawPath R z x)) ((legal_sampleEquiv R _).mpr hc)
    have ha := (stoppingTime_le_iff R _ N).mp ht
    change ¬rawPrefix N (sampleEquiv (Protocol.logicalRawPath R z x)) ∈ active R N at ha
    rw [← toHistory_rawPrefix, active_toHistory, Protocol.logicalRawPath_prefix] at ha
    exact ha
  · intro hn p hp
    obtain ⟨q, rfl⟩ := sampleEquiv.surjective p
    have hq := (legal_sampleEquiv R q).mp hp
    apply (stoppingTime_le_iff R _ N).mpr
    intro ha
    exact hn q.1 (fun n => (q.2 n).getD default) ((active_sampleEquiv R q hq N).mp ha)

def legacyKernel (R : RawRules Z S Ω) (K : Kernel S Ω) (m : ℕ) :
    Kernel (LocalCertification.Information.SlotHistory Z Ω m) (Option Ω) :=
  LocalCertification.Information.stopContinue (Protocol.activePrefix R m) (Protocol.activePrefix_measurable R m)
    (K.comap (Protocol.prefixSetting R m) (Protocol.prefixSetting_measurable R m))

instance legacyKernel_markov (R : RawRules Z S Ω) (K : Kernel S Ω) [IsMarkovKernel K] (m : ℕ) :
    IsMarkovKernel (legacyKernel R K m) := by
  unfold legacyKernel
  infer_instance

/-- Equality of actual original one-copy laws after changing only the padded
label representation. It holds at every prefix, not just almost everywhere. -/
theorem kernel_conjugacy (R : RawRules Z S Ω) (K : Kernel S Ω) (m : ℕ)
    (h : LocalCertification.Information.SlotHistory Z Ω m) :
    (legacyKernel R K m h).map fromOption = stoppedKernel R K m (toHistory m h) := by
  classical
  rw [legacyKernel, LocalCertification.Information.stopContinue_apply, Kernel.comap_apply,
    stoppedKernel_apply, state_toHistory]
  cases ha : (Protocol.execPrefix R m h).2 with
  | inl j =>
    have hn : h ∉ Protocol.activePrefix R m := by simp [Protocol.activePrefix, ha, actionContinues]
    rw [ite_eq_right hn, Measure.map_dirac' fromOption_measurable]
    simp only [collapseState, ha, withAction, fromOption]
  | inr s =>
    have hl : h ∈ Protocol.activePrefix R m := by simp [Protocol.activePrefix, ha, actionContinues]
    rw [ite_eq_left hl, Measure.map_map fromOption_measurable (measurable_of_countable Option.some)]
    simp only [collapseState, ha, withAction, Protocol.prefixSetting, actionSetting, Sum.elim_inr, id_eq]
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

/-- Every finite seed/outcome law is exactly preserved by the representation
map. No conditional-law or path-law identity is assumed. -/
theorem prefixLaw_conjugacy (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] (m : ℕ) :
    (LocalCertification.Information.prefixLaw seed (legacyKernel R K) m).map (toHistory m) =
      LocalCertification.Information.KernelHistory.prefixLaw seed (stoppedKernel R K) m := by
  induction m with
  | zero =>
    change (seed.map ULift.up).map ULift.down = seed
    rw [Measure.map_map measurable_down measurable_up]
    exact Measure.map_id
  | succ m ih =>
    change (LocalCertification.Information.prefixLaw seed (legacyKernel R K) m ⊗ₘ legacyKernel R K m).map
      (Prod.map (toHistory m) fromOption) = _
    rw [map_compProd_conjugacy _ _ (stoppedKernel R K m) _ _ (toHistory_measurable m)
      fromOption_measurable (kernel_conjugacy R K m), ih]
    rfl

/-- The cylinder uniqueness theorem lifts equality of all finite prefix laws to
equality of the two execution laws. -/
theorem stoppedLaw_conjugacy (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] :
    stoppedLaw R seed K = (Protocol.rawTrajectoryLaw seed (legacyKernel R K)).map sampleEquiv := by
  let : IsProbabilityMeasure ((stoppedLaw R seed K).map (sampleEquiv (Z := Z) (Ω := Ω)).symm) := by
    constructor
    rw [Measure.map_apply sampleEquiv.symm.measurable MeasurableSet.univ]
    simp
  have h : (stoppedLaw R seed K).map sampleEquiv.symm = Protocol.rawTrajectoryLaw seed (legacyKernel R K) := by
    apply Protocol.rawLaw_ext_prefix
    intro m
    calc
      ((stoppedLaw R seed K).map sampleEquiv.symm).map (Protocol.rawPrefix m) =
          (stoppedLaw R seed K).map (fromHistory m ∘ rawPrefix m) := by
        rw [Measure.map_map (Protocol.rawPrefix_measurable m) sampleEquiv.symm.measurable]
        congr 1
        funext p
        exact (fromHistory_rawPrefix m p).symm
      _ = ((stoppedLaw R seed K).map (rawPrefix m)).map (fromHistory m) := by
        rw [Measure.map_map (fromHistory_measurable m) (rawPrefix_measurable m)]
      _ = (LocalCertification.Information.KernelHistory.prefixLaw seed (stoppedKernel R K) m).map
          (fromHistory m) := by rw [stoppedLaw_prefix]
      _ = LocalCertification.Information.prefixLaw seed (legacyKernel R K) m := by
        rw [← prefixLaw_conjugacy R seed K m,
          Measure.map_map (fromHistory_measurable m) (toHistory_measurable m),
          show fromHistory m ∘ toHistory m = id from funext (fromHistory_toHistory m), Measure.map_id]
      _ = (Protocol.rawTrajectoryLaw seed (legacyKernel R K)).map (Protocol.rawPrefix m) :=
        (Protocol.rawTrajectoryLaw_prefix seed (legacyKernel R K) m).symm
  apply MeasurableEquiv.map_measurableEquiv_injective (sampleEquiv (Z := Z) (Ω := Ω)).symm
  rw [h, Measure.map_map sampleEquiv.symm.measurable sampleEquiv.measurable,
    show sampleEquiv.symm ∘ sampleEquiv = (id : RawSample Z Ω → RawSample Z Ω) from
      funext sampleEquiv.symm_apply_apply, Measure.map_id]

end LocalCertification.Protocol.MeasurableExecution.Legacy

namespace LocalCertification.Protocol.MeasurableExecution
universe u
variable {Z S Ω : Type u} [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]
  [Inhabited S] [Inhabited Ω] [Fintype Ω] [MeasurableSingletonClass Ω]

theorem exists_legacy_equivalence :
    ∃ e : RawSample Z Ω ≃ᵐ Sample Z (Slot Ω),
      (∀ p, (e p).1 = p.1) ∧
      (∀ p n, (e p).2 n = match p.2 n with
        | none => Sum.inl () | some x => Sum.inr x) ∧
      (∀ (R : RawRules Z S Ω) p,
        Legal R (e p) ↔ ∀ m, ConsistentPrefix R m (Protocol.rawPrefix m p)) ∧
      (∀ (R : RawRules Z S Ω) p, (∀ m, ConsistentPrefix R m (Protocol.rawPrefix m p)) →
        stoppingTime R (e p) = Protocol.stoppingTime R p.1 (fun n => (p.2 n).getD default)) ∧
      (∀ (R : RawRules Z S Ω) p, (∀ m, ConsistentPrefix R m (Protocol.rawPrefix m p)) →
        terminalDecision R (e p) = Protocol.terminalDecision R p.1 (fun n => (p.2 n).getD default)) ∧
      (∀ (R : RawRules Z S Ω) N, Capped R N ↔ EveryPathCap R N) ∧
      (∀ (R : RawRules Z S Ω) (seed : Measure Z) (_ : IsProbabilityMeasure seed)
          (K : Kernel S Ω) (_ : IsMarkovKernel K),
        stoppedLaw R seed K =
          (Protocol.rawTrajectoryLaw seed (fun m => LocalCertification.Information.stopContinue
            (Protocol.activePrefix R m) (Protocol.activePrefix_measurable R m)
            (K.comap (Protocol.prefixSetting R m) (Protocol.prefixSetting_measurable R m)))).map e) :=
  ⟨Legacy.sampleEquiv, fun _ => rfl, fun _ _ => rfl, Legacy.legal_sampleEquiv,
    Legacy.stoppingTime_sampleEquiv, Legacy.terminalDecision_sampleEquiv, Legacy.capped_iff,
    fun R seed _ K _ => Legacy.stoppedLaw_conjugacy R seed K⟩

end LocalCertification.Protocol.MeasurableExecution
