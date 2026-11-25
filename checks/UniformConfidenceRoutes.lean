import LocalCertification.Protocol.UniformFixedBlockConfidence
import LocalCertification.Asymptotic.EulerMomentAsymptotics
import LocalCertification.LegacyPaper
import Lean

open Lean Elab Command
private def releaseRouteRecord (root : String) (passed : Bool)
    (required forbidden : List String) : String :=
  "ROUTE_CHECK\t" ++ (Json.mkObj [("id",toJson root),("passed",toJson passed),
    ("required",toJson required),("forbidden",toJson forbidden),
    ("required_count",toJson required.length),("forbidden_count",toJson forbidden.length)]).compress


open Lean Elab Command
run_elab do
  let env ← getEnv
  let strongRoots := [
    `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_hierarchy,
    `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_criterion,
    `LocalCertification.LegacyPaper.S22,
    `LocalCertification.LegacyPaper.S22_criterion]
  let criterionRoots := [
    `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_criterion,
    `LocalCertification.LegacyPaper.S22_criterion]
  let roots := [`LocalCertification.Protocol.qudit_same_event_continuous_confidence_hierarchy,
    `LocalCertification.Protocol.fixedBlock_log_budget_criterion_continuous_confidence] ++ strongRoots
  let physicalRequired := [
    `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_hierarchy,
    `LocalCertification.Protocol.qudit_same_event_continuous_confidence_hierarchy,
    `LocalCertification.Quantum.fixedBlockSphere_measure,
    `LocalCertification.Quantum.fixedBlockSphere_pure,
    `LocalCertification.Protocol.fixedBlockExpectedBudget_eq,
    `LocalCertification.Protocol.fixedBlockMaximumBudget_eq]
  let criterionRequired := [
    `LocalCertification.Protocol.fixedBlock_degree_zero_iff,
    `LocalCertification.Protocol.fixedBlock_degree_positive_iff]
  let fixedCutoffProjections := [
    `LocalCertification.Protocol.fixedBlock_hierarchy_continuous_confidence,
    `LocalCertification.Protocol.fixedBlock_log_budget_criterion_continuous_confidence,
    `LocalCertification.Protocol.qudit_continuous_confidence_hierarchy]
  let required := [
    `LocalCertification.Protocol.valid_information_high_low_finite_via_product_density,
    `LocalCertification.Protocol.valid_information_low_high_finite_via_product_density,
    `LocalCertification.Protocol.execution_klDiv_le_truncated_cost_finite_via_product_density,
    `LocalCertification.Protocol.terminal_klDiv_of_truncated_bounds_via_product_density,
    `LocalCertification.Information.prefixLaw_stopped_klDiv_le_product_density,
    `LocalCertification.Information.prefixLaw_withDensity_productDensity,
    `LocalCertification.Information.prefixProductLikelihood_log_expand,
    `LocalCertification.Information.integrable_slotLogLikelihood,
    `LocalCertification.Information.sum_negativeRelativeEntropyAtom_le,
    `LocalCertification.Information.sum_positiveRelativeEntropyAtom_le,
    `LocalCertification.Information.binary_klDiv_le_liminf,
    `LocalCertification.Information.binary_klDiv_event_le,
    `LocalCertification.Protocol.execution_expected_truncations,
    `LocalCertification.Protocol.prefixDecisionEvent_probability_tendsto,
    `LocalCertification.Information.binaryRelativeEntropy_deriv_source_paper,
    `LocalCertification.Information.binaryRelativeEntropy_deriv_target,
    `LocalCertification.Information.binaryRelativeEntropy_source_continuous,
    `LocalCertification.Information.binary_klDiv_target_zero,
    `LocalCertification.Information.continuousConfidenceRatio_positive_minimum,
    `CertificationGaussian.Consumers.uniform_haar_orbit_processed_probability_via_packing,
    `CertificationGaussian.sphereScore_lipschitz_via_l1,
    `CertificationGaussian.tensorUnitaryMatrix_operator_close_of_local_frobenius,
    `CertificationGaussian.all_product_score_bound_quartic_radius,
    `CertificationGaussian.weighted_binomial_floor_entropy_bound_termwise,
    `CertificationGaussian.hasDerivAt_weightedEntropy,
    `CertificationGaussian.complexGaussian_four_normal_blocks_finite_inclusion_exclusion,
    `CertificationGaussian.fourWick_expansion_coefficient_via_fiber,
    `CertificationGaussian.fourWickExpansionFiberEquiv_sign,
    `CertificationGaussian.finiteWick_subset_cancellation,
    `CertificationGaussian.haarFourOverlapIntegral_scaled_le_via_incident_holder,
    `CertificationGaussian.pauliFourOverlapIntegral_scaled_le_via_incident_holder]
  let forbidden := [
    `LocalCertification.Protocol.terminal_klDiv_via_product_density,
    `LocalCertification.Protocol.terminal_binary_information,
    `LocalCertification.Protocol.terminal_information_of_errors,
    `LocalCertification.Protocol.execution_klDiv_le_truncated_cost,
    `LocalCertification.Information.testingThreshold_le_binarySupport,
    `LocalCertification.Information.prefixLaw_klDiv_eq_sum,
    `LocalCertification.Information.prefixLaw_stopped_klDiv_le,
    `InformationTheory.klDiv_compProd_eq_add,
    `CertificationGaussian.complexGaussian_four_normal_blocks,
    `CertificationGaussian.complexGaussian_block_wick,
    `CertificationGaussian.gaussianNormalProduct_recursion,
    `CertificationGaussian.three_matching_sixth_bound,
    `CertificationGaussian.weighted_binomial_floor_entropy_bound]
  for root in roots do
    let required := required ++ (if strongRoots.contains root then physicalRequired else []) ++
      (if criterionRoots.contains root then criterionRequired else [])
    let forbidden := forbidden ++ (if strongRoots.contains root then fixedCutoffProjections else [])
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let some val := ci.value? (allowOpaque := true) | continue
      for d in val.getUsedConstants do
        if d.toString.startsWith "LocalCertification." || d.toString.startsWith "CertificationGaussian." ||
            d == `InformationTheory.klDiv_compProd_eq_add then todo := d :: todo
    for n in required do
      unless seen.contains n do throwError "Required substantive dependency missing: {root} -> {n}"
      logInfo m!"REQUIRED {root} -> {n}"
    for n in forbidden do
      if seen.contains n then throwError "Forbidden old bypass: {root} -> {n}"
    logInfo m!"FINAL_CHAIN_REVIEW_PASS {root}: {seen.size} own constants"
    logInfo (releaseRouteRecord root.toString true (required.map toString) (forbidden.map toString))

open MeasureTheory InformationTheory Set LocalCertification.Information LocalCertification.Protocol
open scoped ENNReal
noncomputable section
example (δ : ℝ) (hδ : 0<δ) (hhalf : δ<1/2) :
    ENNReal.ofReal (testingThreshold δ) ≤ klDiv (binaryMeasure 1) (binaryMeasure 0) :=
  testingThreshold_le_binary_klDiv_via_derivatives δ hδ hhalf 1 0 (by norm_num; linarith) (by simpa using hδ.le)
example (δ : ℝ) (hδ : 0<δ) (hhalf : δ<1/2) (q : Icc (0:ℝ) 1) (hq : (q:ℝ)≤δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ klDiv (binaryMeasure 1) (binaryMeasure q) :=
  testingThreshold_le_binary_klDiv_via_derivatives δ hδ hhalf 1 q (by norm_num; linarith) hq
example (q : ℝ) (hq : 1<q) (j : ℕ) :
    LocalCertification.Asymptotic.criticalDegree q (LocalCertification.Extremal.gamma q j)=j+1 :=
  LocalCertification.Asymptotic.criticalDegree_at_critical_value q hq j
example : continuousConfidenceRatio (1/2)=0 := by norm_num [continuousConfidenceRatio]
example : testingThreshold (1/2)=0 := by norm_num [testingThreshold]
example : ∃ c : ℝ, 0<c ∧ ∀ δ : ℝ, 0<δ → δ≤49/100 →
    c*Real.log (1/δ)≤testingThreshold δ :=
  testingThreshold_confidence_lower_via_continuous_ratio (49/100) (by norm_num) (by norm_num)
#check @terminal_klDiv_finite_via_product_density
#check @valid_information_high_low_finite_via_product_density
#check @valid_information_low_high_finite_via_product_density
#check @calibrated_terminal_information_finite_via_product_density
#check @qudit_same_event_continuous_confidence_hierarchy
#check @fixedBlock_log_budget_criterion_continuous_confidence
#check @fixedBlock_same_event_continuous_confidence_hierarchy
#check @fixedBlock_same_event_continuous_confidence_criterion
#check @LocalCertification.LegacyPaper.S22
#check @LocalCertification.LegacyPaper.S22_criterion
#check @LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion
#print axioms terminal_klDiv_finite_via_product_density
#print axioms valid_information_high_low_finite_via_product_density
#print axioms valid_information_low_high_finite_via_product_density
#print axioms qudit_same_event_continuous_confidence_hierarchy
#print axioms fixedBlock_log_budget_criterion_continuous_confidence
#print axioms fixedBlock_same_event_continuous_confidence_hierarchy
#print axioms fixedBlock_same_event_continuous_confidence_criterion
#print axioms LocalCertification.LegacyPaper.S22
#print axioms LocalCertification.LegacyPaper.S22_criterion
#print axioms LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion
