import LocalCertification.Protocol.TreeBornPrefix
import LocalCertification.Protocol.RawLawExt

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- Full actual infinite execution laws agree after mapping the retained old seed to its tree.
No inverse recovering the old seed is asserted: the seed-to-tree map may be many-to-one. -/
theorem imageTreeProtocol_executionLaw (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (executionLaw P ρ).map (mapRawSeed (seedToTree P.toRawRules)) = executionLaw (imageTreeProtocol P) ρ := by
  have hf := mapRawSeed_measurable (O := CertificationGaussian.QuditIndex d n) _ (seedToTree_measurable P.toRawRules)
  let : IsProbabilityMeasure ((executionLaw P ρ).map (mapRawSeed (seedToTree P.toRawRules))) := by
    constructor
    rw [Measure.map_apply hf MeasurableSet.univ]
    simp
  apply rawLaw_ext_prefix
  intro m
  rw [Measure.map_map (rawPrefix_measurable m) hf, executionLaw_prefix]
  have he : rawPrefix (O := CertificationGaussian.QuditIndex d n) m ∘ mapRawSeed (seedToTree P.toRawRules) =
      mapSlotSeed (seedToTree P.toRawRules) m ∘ rawPrefix m := by
    funext p
    exact (mapSlotSeed_rawPrefix _ m p).symm
  rw [he, ← Measure.map_map (mapSlotSeed_measurable _ (seedToTree_measurable P.toRawRules) m)
    (rawPrefix_measurable m), executionLaw_prefix, imageTreeProtocol_prefixLaw]

/-- Time preservation holds on every raw sample, not only almost surely. -/
theorem imageTreeProtocol_time (P : QuditProtocol Z d n) (p : RawSample Z (CertificationGaussian.QuditIndex d n)) :
    executionTime (imageTreeProtocol P) (mapRawSeed (seedToTree P.toRawRules) p) = executionTime P p :=
  treeRules_stoppingTime_eq P.toRawRules p.1 (fun m => (p.2 m).getD default)

theorem imageTreeProtocol_decision (P : QuditProtocol Z d n) (p : RawSample Z (CertificationGaussian.QuditIndex d n)) :
    executionDecision (imageTreeProtocol P) (mapRawSeed (seedToTree P.toRawRules) p) = executionDecision P p :=
  treeRules_terminalDecision_eq P.toRawRules p.1 (fun m => (p.2 m).getD default)

theorem imageTreeProtocol_cost (P : QuditProtocol Z d n) (p : RawSample Z (CertificationGaussian.QuditIndex d n)) :
    executionCost (imageTreeProtocol P) (mapRawSeed (seedToTree P.toRawRules) p) = executionCost P p :=
  congrArg ENat.toENNReal (imageTreeProtocol_time P p)

/-- Every physical input has exactly the same extended expected copies, including infinity. -/
theorem imageTreeProtocol_expectedCopies (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : expectedCopies (imageTreeProtocol P) ρ = expectedCopies P ρ := by
  unfold expectedCopies
  rw [← imageTreeProtocol_executionLaw, lintegral_map (executionCost_measurable (imageTreeProtocol P))
    (mapRawSeed_measurable _ (seedToTree_measurable P.toRawRules))]
  apply lintegral_congr
  exact imageTreeProtocol_cost P

/-- Almost-sure termination is preserved separately under each actual input law. -/
theorem imageTreeProtocol_terminates_iff (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : Terminates (imageTreeProtocol P) ρ ↔ Terminates P ρ := by
  unfold Terminates
  rw [← imageTreeProtocol_executionLaw]
  have hm : MeasurableSet {p | executionTime (imageTreeProtocol P) p ≠ ⊤} :=
    (((executionTime_measurable (imageTreeProtocol P)) (measurableSet_singleton ⊤)).compl)
  rw [ae_map_iff (mapRawSeed_measurable _ (seedToTree_measurable P.toRawRules)).aemeasurable hm]
  simp only [imageTreeProtocol_time]

theorem imageTreeProtocol_decision_measure (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : Fin 2) :
    executionLaw (imageTreeProtocol P) ρ {p | executionDecision (imageTreeProtocol P) p = j} =
      executionLaw P ρ {p | executionDecision P p = j} := by
  have hm : MeasurableSet {p | executionDecision (imageTreeProtocol P) p = j} :=
    (executionDecision_measurable (imageTreeProtocol P)) (measurableSet_singleton j)
  rw [← imageTreeProtocol_executionLaw, Measure.map_apply
    (mapRawSeed_measurable _ (seedToTree_measurable P.toRawRules)) hm]
  congr 1
  ext p
  change executionDecision (imageTreeProtocol P) (mapRawSeed (seedToTree P.toRawRules) p) = j ↔ executionDecision P p = j
  rw [imageTreeProtocol_decision]

/-- Complete validity, with only promise termination and averaged errors, is equivalent under full-image normalization. -/
theorem imageTreeProtocol_valid_iff (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    Valid (imageTreeProtocol P) ψ a b δ ↔ Valid P ψ a b δ := by
  unfold Valid
  simp only [imageTreeProtocol_terminates_iff, imageTreeProtocol_decision_measure]

end LocalCertification.Protocol
