import LocalCertification.Protocol.LegalFiltration

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- Every legal finite prefix has the actual iterated physical law. -/
theorem legalPathLaw_prefix (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    (legalPathLaw P ρ).map (fun p : legalPaths P.toRawRules => rawPrefix m p.val) = executionPrefixLaw P ρ m := by
  calc
    _ = ((legalPathLaw P ρ).map Subtype.val).map (rawPrefix m) := by
      rw [Measure.map_map (rawPrefix_measurable m) measurable_subtype_coe]
      rfl
    _ = _ := by rw [legalPathLaw_map, executionLaw_prefix]

/-- The actual legal-path seed marginal is the single source-independent seed law. -/
theorem legalPathLaw_seed (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (legalPathLaw P ρ).map (fun p : legalPaths P.toRawRules => p.val.1) = P.seedLaw := by
  have h0 : (legalPathLaw P ρ).map (fun p : legalPaths P.toRawRules => (ULift.up p.val.1 : ULift.{0} Z)) =
      P.seedLaw.map (ULift.up : Z → ULift.{0} Z) := legalPathLaw_prefix P ρ 0
  have h := congrArg (fun μ : Measure (ULift.{0} Z) => μ.map ULift.down) h0
  have hm : Measurable (fun p : legalPaths P.toRawRules => (ULift.up p.val.1 : ULift.{0} Z)) :=
    measurable_up.comp (measurable_fst.comp measurable_subtype_coe)
  have hl := Measure.map_map (μ := legalPathLaw P ρ)
    (show Measurable (ULift.down : ULift.{0} Z → Z) from measurable_down) hm
  have hr := Measure.map_map (μ := P.seedLaw)
    (show Measurable (ULift.down : ULift.{0} Z → Z) from measurable_down)
    (show Measurable (ULift.up : Z → ULift.{0} Z) from measurable_up)
  exact hl.symm.trans (h.trans (hr.trans Measure.map_id))

/-- On a requested copy the actual stopped kernel draws precisely the existing QIT Born atom. -/
theorem executionSlotKernel_born_atom (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ)
    (h : SlotHistory Z (CertificationGaussian.QuditIndex d n) m) (ha : h ∈ activePrefix P.toRawRules m)
    (x : CertificationGaussian.QuditIndex d n) :
    executionSlotKernel P ρ m h {some x} =
      ENNReal.ofReal (productBorn d n (prefixSetting P.toRawRules m h) ρ x) := by
  rw [executionSlotKernel, stopContinue_apply, ite_eq_left ha,
    Measure.map_apply (measurable_of_countable Option.some) (measurableSet_singleton (some x))]
  have he : Option.some ⁻¹' ({some x} : Set (Option (CertificationGaussian.QuditIndex d n))) = {x} := by
    ext y
    simp
  rw [he]
  change productBornMeasure d n (prefixSetting P.toRawRules m h) ρ {x} = _
  rw [← productBornMeasure_atom_real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The finite rectangle identity comes directly from the actual compProd recursion, without conditioning on seed fibers. -/
theorem executionPrefixLaw_born_rectangle (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ)
    (A : Set (SlotHistory Z (CertificationGaussian.QuditIndex d n) m)) (hA : MeasurableSet A)
    (x : CertificationGaussian.QuditIndex d n) :
    executionPrefixLaw P ρ (m+1) ((A ∩ activePrefix P.toRawRules m) ×ˢ {some x}) =
      ∫⁻ h in A ∩ activePrefix P.toRawRules m,
        ENNReal.ofReal (productBorn d n (prefixSetting P.toRawRules m h) ρ x) ∂executionPrefixLaw P ρ m := by
  change (executionPrefixLaw P ρ m ⊗ₘ executionSlotKernel P ρ m) _ = _
  rw [Measure.compProd_apply_prod (hA.inter (activePrefix_measurable P.toRawRules m))
    (measurableSet_singleton (some x))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hA.inter (activePrefix_measurable P.toRawRules m))] with h hh
  exact executionSlotKernel_born_atom P ρ m h hh.2 x

/-- Every raw finite-filtration event satisfies the genuine conditional Born integral identity.
Only the action target has topology; neither seed nor history requires standard-Borel structure or disintegration. -/
theorem legal_conditionalBorn (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ)
    (A : Set (legalPaths P.toRawRules)) (hA : MeasurableSet[legalFiltration P.toRawRules m] A)
    (x : CertificationGaussian.QuditIndex d n) :
    legalPathLaw P ρ (A ∩ {p | (m : WithTop ℕ) < executionTime P p.val} ∩ {p | p.val.2 m = some x}) =
      ∫⁻ p in A ∩ {p | (m : WithTop ℕ) < executionTime P p.val},
        ENNReal.ofReal (productBorn d n (prefixSetting P.toRawRules m (rawPrefix m p.val)) ρ x) ∂legalPathLaw P ρ := by
  obtain ⟨B,hB,rfl⟩ := hA
  have hpre : Measurable (fun p : legalPaths P.toRawRules => rawPrefix m p.val) :=
    (rawPrefix_measurable m).comp measurable_subtype_coe
  have hnext : Measurable (fun p : legalPaths P.toRawRules => rawPrefix (m+1) p.val) :=
    (rawPrefix_measurable (m+1)).comp measurable_subtype_coe
  have hb : Measurable (fun h => ENNReal.ofReal (productBorn d n (prefixSetting P.toRawRules m h) ρ x)) :=
    ((productBorn_continuous d n ρ x).measurable.comp (prefixSetting_measurable P.toRawRules m)).ennreal_ofReal
  have ha (p : legalPaths P.toRawRules) : (m : WithTop ℕ) < executionTime P p.val ↔
      rawPrefix m p.val ∈ activePrefix P.toRawRules m := by
    rw [lt_iff_not_ge, legalPath_stoppingTime_le]
    exact not_not
  have hi := executionPrefixLaw_born_rectangle P ρ m B hB x
  rw [← legalPathLaw_prefix P ρ (m+1), Measure.map_apply hnext
      ((hB.inter (activePrefix_measurable P.toRawRules m)).prod (measurableSet_singleton (some x))),
    ← legalPathLaw_prefix P ρ m,
    setLIntegral_map (hB.inter (activePrefix_measurable P.toRawRules m)) hb hpre] at hi
  have he : (fun p : legalPaths P.toRawRules => rawPrefix m p.val) ⁻¹' B ∩
      {p | (m : WithTop ℕ) < executionTime P p.val} =
      (fun p : legalPaths P.toRawRules => rawPrefix m p.val) ⁻¹' (B ∩ activePrefix P.toRawRules m) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, ha]
  rw [he]
  convert hi using 1
  congr 1

/-- Restricted to an event on which the next copy is requested, no active indicator is needed. -/
theorem legal_conditionalBorn_of_active (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ)
    (A : Set (legalPaths P.toRawRules)) (hA : MeasurableSet[legalFiltration P.toRawRules m] A)
    (ha : A ⊆ {p | (m : WithTop ℕ) < executionTime P p.val}) (x : CertificationGaussian.QuditIndex d n) :
    legalPathLaw P ρ (A ∩ {p | p.val.2 m = some x}) =
      ∫⁻ p in A, ENNReal.ofReal
        (productBorn d n (prefixSetting P.toRawRules m (rawPrefix m p.val)) ρ x) ∂legalPathLaw P ρ := by
  simpa only [Set.inter_eq_left.mpr ha] using legal_conditionalBorn P ρ m A hA x

end LocalCertification.Protocol
