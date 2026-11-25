import LocalCertification
import Lean
set_option maxHeartbeats 0
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.maxSteps 100000000
open Lean Elab Command
run_elab do
  let env ← getEnv
  let suites : List (Name × List Name × List Name) := [
    (`CertificationGaussian.haar_unitaryDephasing_entry,
      [`CertificationGaussian.haar_column_fourth_moment_symmetric,
       `CertificationGaussian.haar_column_tensor_eq_normalized_symmetric_projection], []),
    (`LocalCertification.Paper.S11_Haar,
      [`CertificationGaussian.complexSphere_squaredOverlap_beta], []),
    (`LocalCertification.Paper.theorem_3_wiener,
      [`LocalCertification.Asymptotic.Wiener.inversion_of_bounds,
       `LocalCertification.Asymptotic.Wiener.gamma_sharp_order,
       `LocalCertification.Asymptotic.Wiener.interpolation_sandwich,
       `LocalCertification.Asymptotic.Wiener.finite_dual_attains,
       `LocalCertification.Asymptotic.Wiener.real_projection,
       `LocalCertification.Asymptotic.Wiener.derivatives_iff_polynomial_moments,
       `LocalCertification.Asymptotic.Wiener.szehr_zarouf_lower,
       `LocalCertification.Asymptotic.Wiener.schaffer_upper],
      [`LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion]),
    (`LocalCertification.Paper.S22_finite_high_weight_maxima,
      [`CertificationGaussian.radialFirstCoefficient_bound_of_le], []),
    (`LocalCertification.Paper.S22_weight_estimates,
      [`CertificationGaussian.finite_square_mass_le,
       `CertificationGaussian.radialFirstCoefficient_abs_mass,
       `CertificationGaussian.complementLambda_le_polynomial], []),
    (`LocalCertification.Paper.qubit_table,
      [`LocalCertification.Manuscript.qubit_quadratic_ratio_antitone,
       `LocalCertification.Manuscript.quartic_interpolation], []),
    (`LocalCertification.Paper.tolerance_hierarchy, [`LocalCertification.Quantum.measurableExponential_hard_states, `CertificationGaussian.productFrame_common_sphere_eventually, `LocalCertification.Quantum.dualResidualQuadratic_eq_productFrameSphereScore, `LocalCertification.Quantum.MeasurablePOVM.productRefined_born_map, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.expectedBudget_lower_high_low, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.expectedBudget_lower_low_high, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_high_low, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_low_high, `LocalCertification.Information.continuousConfidenceRatio_positive_minimum, `LocalCertification.Quantum.MeasurablePOVM.sum_refinementEffect, `LocalCertification.Quantum.sum_selectedEigenvalue_rankOne, `LocalCertification.Quantum.measurable_ordered_eigenvalues, `LocalCertification.Quantum.calibrated_product_klDiv_le_kernel, `LocalCertification.Quantum.MeasurablePOVM.product_klDiv_le_localRefinement, `LocalCertification.Quantum.MeasurablePOVM.calibrated_denominator_floor, `LocalCertification.Quantum.MeasurablePOVM.productRefined_reference_sq_eq], [`LocalCertification.Quantum.exponentialHaar_hard_states, `LocalCertification.Protocol.qudit_same_event_continuous_confidence_hierarchy, `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_hierarchy, `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_criterion]),
    (`LocalCertification.Paper.near_critical_transition, [`LocalCertification.Quantum.measurableExponential_hard_states_uniform, `CertificationGaussian.productFrame_common_sphere_eventually, `LocalCertification.Quantum.dualResidualQuadratic_eq_productFrameSphereScore, `LocalCertification.Quantum.MeasurablePOVM.productRefined_born_map, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.expectedBudget_lower_high_low, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.expectedBudget_lower_low_high, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_high_low, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_low_high, `LocalCertification.Quantum.measurableNearCritical_positive_eventually_uniform, `LocalCertification.Quantum.measurableNearCritical_zero_eventually_uniform, `LocalCertification.Quantum.NearCriticalAdjacent.born_klDiv_le_rate, `LocalCertification.Quantum.MeasurablePOVM.nearCriticalZero_born_klDiv_rate, `LocalCertification.Quantum.pure_product_referenceL2_sq_le_of_frameFamily, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_upper_uniform, `LocalCertification.Information.continuousConfidenceRatio_positive_minimum], [`LocalCertification.Quantum.exponentialHaar_hard_states, `LocalCertification.Protocol.qudit_same_event_continuous_confidence_hierarchy, `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_hierarchy, `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_criterion]),
    (`LocalCertification.Paper.fixed_block_hierarchy, [`LocalCertification.Quantum.measurableExponential_hard_states, `CertificationGaussian.productFrame_common_sphere_eventually, `LocalCertification.Quantum.dualResidualQuadratic_eq_productFrameSphereScore, `LocalCertification.Quantum.MeasurablePOVM.productRefined_born_map, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.expectedBudget_lower_high_low, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.expectedBudget_lower_low_high, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_high_low, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_low_high, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.product_budget_sphere_hierarchy, `LocalCertification.Protocol.MeasurableExecution.FixedBlock.expectedBudget_eq, `LocalCertification.Protocol.MeasurableExecution.FixedBlock.maximumBudget_eq, `LocalCertification.Quantum.fixedBlockSphere_measure, `LocalCertification.Information.continuousConfidenceRatio_positive_minimum, `LocalCertification.Quantum.MeasurablePOVM.sum_refinementEffect, `LocalCertification.Quantum.sum_selectedEigenvalue_rankOne, `LocalCertification.Quantum.measurable_ordered_eigenvalues, `LocalCertification.Quantum.calibrated_product_klDiv_le_kernel, `LocalCertification.Quantum.MeasurablePOVM.product_klDiv_le_localRefinement, `LocalCertification.Quantum.MeasurablePOVM.calibrated_denominator_floor, `LocalCertification.Quantum.MeasurablePOVM.productRefined_reference_sq_eq], [`LocalCertification.Quantum.exponentialHaar_hard_states, `LocalCertification.Protocol.qudit_same_event_continuous_confidence_hierarchy, `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_hierarchy, `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_criterion]),
    (`LocalCertification.Paper.sharp_decay_and_inversion, [`LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion, `LocalCertification.Asymptotic.EulerMoments.eulerExpansion_succ, `LocalCertification.Asymptotic.EulerMoments.gamma_blaschke_lower, `LocalCertification.Asymptotic.EulerMoments.criticalDegree_log_bracket], [`LocalCertification.Asymptotic.sharp_order_and_inversion]),
    (`LocalCertification.Paper.corollary_2, [`LocalCertification.Quantum.measurableExponential_hard_states_uniform, `CertificationGaussian.productFrame_common_sphere_eventually, `LocalCertification.Quantum.dualResidualQuadratic_eq_productFrameSphereScore, `LocalCertification.Quantum.MeasurablePOVM.productRefined_born_map, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.expectedBudget_lower_high_low, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.expectedBudget_lower_low_high, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_high_low, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_low_high, `LocalCertification.Quantum.measurableNearCritical_positive_eventually_uniform, `LocalCertification.Quantum.measurableNearCritical_zero_eventually_uniform, `LocalCertification.Quantum.NearCriticalAdjacent.born_klDiv_le_rate, `LocalCertification.Quantum.MeasurablePOVM.nearCriticalZero_born_klDiv_rate, `LocalCertification.Quantum.pure_product_referenceL2_sq_le_of_frameFamily, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_upper_uniform, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_neighborhood_confidence, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_confidence_uniform, `LocalCertification.Information.continuousConfidenceRatio_positive_minimum, `LocalCertification.Protocol.MeasurableExecution.nearCriticalScale_compare_costOrder, `LocalCertification.Quantum.eventually_calibration_overlap_window], [`LocalCertification.Quantum.exponentialHaar_hard_states, `LocalCertification.Protocol.qudit_same_event_continuous_confidence_hierarchy, `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_hierarchy, `LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_criterion]),
    (`LocalCertification.Paper.theorem_3, [`LocalCertification.Manuscript.sharp_order_and_inversion, `LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion], []),
    (`LocalCertification.Paper.qubit_quartic, [`LocalCertification.Manuscript.quartic_interpolation, `LocalCertification.Manuscript.quartic_envelope_bound], []),
    (`LocalCertification.Paper.S19,
      [`LocalCertification.Quantum.calibrated_product_klDiv_le_kernel,
       `LocalCertification.Quantum.MeasurablePOVM.product_klDiv_le_localRefinement,
       `LocalCertification.Quantum.MeasurablePOVM.calibrated_denominator_floor,
       `LocalCertification.Quantum.MeasurablePOVM.productRefined_reference_sq_eq,
       `LocalCertification.Quantum.MeasurablePOVM.sum_refinementEffect,
       `LocalCertification.Quantum.sum_selectedEigenvalue_rankOne,
       `LocalCertification.Quantum.measurable_ordered_eigenvalues,
       `LocalCertification.Quantum.calibrated_refined_referenceL2_le_kernel,
       `LocalCertification.Quantum.calibrated_product_referenceL2_le_kernel,
       `LocalCertification.Quantum.MeasurablePOVM.calibrated_chiSquare_norm_le], []),
    (`LocalCertification.Paper.S8_Pauli_quantitative, [`LocalCertification.Protocol.full_control_canonical_targets, `LocalCertification.Quantum.completeReadoutLoewner_of_full_control, `CertificationGaussian.cardinalityPauli_remainder_bound], []),
    (`LocalCertification.Paper.S8_Haar_quantitative, [`LocalCertification.Protocol.full_control_canonical_targets, `LocalCertification.Quantum.completeReadoutLoewner_of_full_control, `CertificationGaussian.cardinalityHaar_remainder_bound], []),
    (`LocalCertification.Paper.S15_quantitative, [`LocalCertification.Protocol.full_control_canonical_targets, `LocalCertification.Quantum.completeReadoutLoewner_of_full_control, `CertificationGaussian.cardinalityMUB_remainder_bound], []),
    (`LocalCertification.Paper.history_budget_equivalence, [`LocalCertification.Protocol.MeasurableExecution.PaperHistoryBudget.expectedBudget_eq, `LocalCertification.Protocol.MeasurableExecution.PaperHistoryBudget.maximumBudget_eq, `LocalCertification.Protocol.MeasurableExecution.PaperHistoryProduct.exists_compile, `LocalCertification.Protocol.MeasurableExecution.PaperHistoryProduct.exists_compile_of_live, `LocalCertification.Protocol.MeasurableExecution.PaperHistoryProduct.emptyCompile_preserves, `LocalCertification.Quantum.POVMKernel.exists_product_factors, `LocalCertification.Protocol.MeasurableExecution.HistoryProductProtocol.compile_law, `LocalCertification.Protocol.MeasurableExecution.HistoryEncoding.state_projection, `LocalCertification.Protocol.MeasurableExecution.HistoryEncoding.state_context, `LocalCertification.Protocol.MeasurableExecution.PaperHistoryProduct.ofSetting_preserves], [])]
  for (root, required, forbidden) in suites do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let some val := ci.value? (allowOpaque := true) | continue
      for dep in val.getUsedConstants do
        let some idx := env.getModuleIdxFor? dep | continue
        let owner := env.header.moduleNames[idx.toNat]!.toString
        if owner.startsWith "LocalCertification" || owner.startsWith "CertificationGaussian." then
          todo := dep :: todo
    for n in required do
      unless seen.contains n do throwError "Missing actual proof dependency: {root} -> {n}"
    for n in forbidden do
      if seen.contains n then throwError "Legacy theorem used for general POVM lower bound: {root} -> {n}"
    logInfo m!"ROUTE_CHECK\t{(Json.mkObj [("id", toJson root.toString), ("passed", toJson true),
      ("required", toJson (required.map toString)), ("forbidden", toJson (forbidden.map toString)),
      ("visited_owned_declarations", toJson seen.size)]).compress}"
