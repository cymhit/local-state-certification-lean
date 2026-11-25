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
  let aliases : List (Name × Name) := [
    (`LocalCertification.Paper.tolerance_hierarchy, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.product_budget_same_event_confidence_hierarchy),
    (`LocalCertification.Paper.tolerance_testing_bounds, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.product_budget_sphere_hierarchy),
    (`LocalCertification.Paper.tolerance_haar_bounds, `LocalCertification.Protocol.MeasurableExecution.ProductBudget.product_budget_haar_hierarchy),
    (`LocalCertification.Paper.near_critical_transition, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_confidence_hierarchy),
    (`LocalCertification.Paper.near_critical_testing_bounds, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_hierarchy),
    (`LocalCertification.Paper.sharp_decay_and_inversion, `LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion),
    (`LocalCertification.Paper.fixed_block_hierarchy, `LocalCertification.Protocol.MeasurableExecution.FixedBlock.fixedBlock_budget_same_event_confidence_hierarchy),
    (`LocalCertification.Paper.fixed_block_testing_bounds, `LocalCertification.Protocol.MeasurableExecution.FixedBlock.fixedBlock_budget_sphere_hierarchy),
    (`LocalCertification.Paper.fixed_block_threshold, `LocalCertification.Protocol.MeasurableExecution.FixedBlock.fixedBlock_budget_same_event_criterion),
    (`LocalCertification.Paper.history_model_compilation, `LocalCertification.Protocol.MeasurableExecution.PaperHistoryProduct.exists_compile),
    (`LocalCertification.Paper.history_budget_equivalence, `LocalCertification.Protocol.MeasurableExecution.PaperHistoryBudget.budget_equivalence),
    (`LocalCertification.Paper.theorem_1, `LocalCertification.Paper.tolerance_hierarchy),
    (`LocalCertification.Paper.corollary_2, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_neighborhood_confidence),
    (`LocalCertification.Paper.theorem_3, `LocalCertification.Manuscript.physical_sharp_order_and_inversion),
    (`LocalCertification.Paper.theorem_3_wiener, `LocalCertification.Manuscript.physical_wiener_sharp_order_and_inversion),
    (`LocalCertification.Paper.qubit_table, `LocalCertification.Manuscript.qubit_critical_values),
    (`LocalCertification.Paper.low_degree_values, `LocalCertification.Manuscript.low_degree_values),
    (`LocalCertification.Paper.S7_bound, `LocalCertification.Extremal.GeometricSeries.gamma_binomial_bound),
    (`LocalCertification.Paper.S7_decay, `LocalCertification.Extremal.GeometricSeries.gamma_tendsto_zero_of_two_lt),
    (`LocalCertification.Paper.S8_Haar, `LocalCertification.Quantum.completeHaarReadout_scorebounds),
    (`LocalCertification.Paper.S8_Pauli, `LocalCertification.Quantum.completePauliReadout_scorebounds),
    (`LocalCertification.Paper.S8_Haar_protocol, `LocalCertification.Protocol.fixedScore_haar_canonical),
    (`LocalCertification.Paper.S8_Pauli_protocol, `LocalCertification.Protocol.fixedScore_pauli_canonical),
    (`LocalCertification.Paper.S11_Haar, `CertificationGaussian.haar_local_graph_contraction_via_incident_holder),
    (`LocalCertification.Paper.S11_Pauli, `CertificationGaussian.pauli_local_graph_contraction_via_incident_holder),
    (`LocalCertification.Paper.S11_MUB, `CertificationGaussian.completeMUB_local_graph_contraction_via_incident_holder),
    (`LocalCertification.Paper.S12_Wick, `CertificationGaussian.complexGaussian_four_normal_blocks_finite_inclusion_exclusion),
    (`LocalCertification.Paper.S12_Wick_bound, `CertificationGaussian.complexGaussian_four_normal_blocks_finite_norm_le),
    (`LocalCertification.Paper.S12_Haar, `CertificationGaussian.cardinalityHaar_remainder_bound),
    (`LocalCertification.Paper.S12_Pauli, `CertificationGaussian.cardinalityPauli_remainder_bound),
    (`LocalCertification.Paper.S15, `LocalCertification.Protocol.fixedScore_completeMUB_canonical),
    (`LocalCertification.Paper.S15_basis_upper, `LocalCertification.Protocol.completeMUB_corollary_three_six),
    (`LocalCertification.Paper.S16_kernel_moments, `CertificationGaussian.cardinalityProjectorKernel_moments),
    (`LocalCertification.Paper.S17, `LocalCertification.Quantum.weylShell_complement_readout),
    (`LocalCertification.Paper.S18_sphere, `CertificationGaussian.productFrame_common_sphere_eventually),
    (`LocalCertification.Paper.S18_Haar, `CertificationGaussian.productFrame_common_haar_eventually),
    (`LocalCertification.Paper.S18_zero_radius, `LocalCertification.Quantum.pure_product_referenceL2_sq_le_of_frameFamily),
    (`LocalCertification.Paper.S19, `LocalCertification.Quantum.measurableExponential_hard_states),
    (`LocalCertification.Paper.S19_background, `LocalCertification.Quantum.MeasurablePOVM.calibrated_denominator_floor),
    (`LocalCertification.Paper.S22_finite_high_weight_maxima, `LocalCertification.Quantum.finite_high_weight_maxima),
    (`LocalCertification.Paper.S22_weight_estimates, `LocalCertification.Quantum.weyl_weight_estimates),
    (`LocalCertification.Paper.S20_high_low, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_high_low),
    (`LocalCertification.Paper.S20_low_high, `LocalCertification.Protocol.MeasurableExecution.BornProtocol.information_of_valid_low_high),
    (`LocalCertification.Paper.S21, `LocalCertification.Paper.tolerance_testing_bounds),
    (`LocalCertification.Paper.S22, `LocalCertification.Paper.tolerance_hierarchy),
    (`LocalCertification.Paper.S23, `LocalCertification.Paper.fixed_block_hierarchy),
    (`LocalCertification.Paper.S23_criterion, `LocalCertification.Paper.fixed_block_threshold),
    (`LocalCertification.Paper.S25, `LocalCertification.Manuscript.blaschke_lower),
    (`LocalCertification.Paper.S25_coefficient, `LocalCertification.Manuscript.blaschke_coefficient_lower),
    (`LocalCertification.Paper.S30, `LocalCertification.Manuscript.certificate_optimality),
    (`LocalCertification.Paper.S31, `LocalCertification.Manuscript.certificate_exists),
    (`LocalCertification.Paper.S32_termination, `LocalCertification.Manuscript.certificate_search_terminates),
    (`LocalCertification.Paper.S32_correct, `LocalCertification.Manuscript.certificate_output_correct),
    (`LocalCertification.Paper.S33, `LocalCertification.Manuscript.low_degree_values),
    (`LocalCertification.Paper.near_critical_neighborhood, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_neighborhood),
    (`LocalCertification.Paper.near_critical_window, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_hierarchy_uniform),
    (`LocalCertification.Paper.near_critical_window_confidence, `LocalCertification.Protocol.MeasurableExecution.qudit_nearCritical_product_confidence_uniform),
    (`LocalCertification.Paper.S6_even_endpoints, `LocalCertification.Manuscript.optimizer_endpoints_even),
    (`LocalCertification.Paper.S6_odd_endpoints, `LocalCertification.Manuscript.optimizer_endpoints_odd),
    (`LocalCertification.Paper.qubit_quartic, `LocalCertification.Manuscript.qubit_quartic_exact),
    (`LocalCertification.Paper.S8_Haar_quantitative, `LocalCertification.Protocol.quantitativeScoreBounds_haar),
    (`LocalCertification.Paper.S8_Pauli_quantitative, `LocalCertification.Protocol.quantitativeScoreBounds_pauli),
    (`LocalCertification.Paper.S15_quantitative, `LocalCertification.Protocol.quantitativeScoreBounds_completeMUB),
    (`LocalCertification.Paper.S15_protocol_quantitative, `LocalCertification.Protocol.fixedScore_completeMUB_quantitative),
    (`LocalCertification.Paper.global_comparison, `LocalCertification.Comparisons.global_projector_comparison)]
  for (n, target) in aliases do
    let some ci := env.find? n | throwError "Missing public alias: {n}"
    let some val := ci.value? (allowOpaque := true) | throwError "Public alias has no proof: {n}"
    unless val.getUsedConstants.contains target do
      throwError "Public alias target differs: {n}, expected {target}"
    let ty := (← Meta.ppExpr ci.type).pretty 160
    if ty.contains '⋯' || ty.contains '…' then throwError "Abbreviated public type: {n}"
    logInfo m!"MAPPING_CHECK\t{(Json.mkObj [("declaration", toJson n.toString),
      ("target", toJson target.toString), ("type", toJson ty),
      ("level_parameters", toJson (ci.levelParams.map toString))]).compress}"
