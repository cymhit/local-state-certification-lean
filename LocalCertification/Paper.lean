import LocalCertification.Protocol.MeasurableHaarHierarchy
import LocalCertification.Protocol.MeasurableNearCriticalHierarchy
import LocalCertification.Protocol.NearCriticalNeighborhood
import LocalCertification.Protocol.MeasurableFixedBlockHierarchy
import LocalCertification.Protocol.MeasurableExecutionOriginalBudgets
import LocalCertification.Protocol.MeasurableHistoryBudgets
import LocalCertification.Protocol.MeasurableFixedBlockOriginal
import LocalCertification.Asymptotic.EulerMomentAsymptotics
import LocalCertification.Asymptotic.WienerInversion
import LocalCertification.Extremal.GeometricSeriesDecay
import LocalCertification.Certificates.StagedSearchConsumers
import LocalCertification.Certificates.RealLowDegreeConsumers
import LocalCertification.Certificates.DimensionStatements
import LocalCertification.Extremal.ParityEnvelopes
import LocalCertification.Comparisons.GlobalProjectorTest
import LocalCertification.Protocol.FixedScoreAchievabilityConsumers
import LocalCertification.Protocol.CompleteMUBAchievabilityConsumers
import LocalCertification.Protocol.QuantitativeReadoutEnsembles
import LocalCertification.Quantum.CompleteReadoutLoewner
import LocalCertification.Quantum.FrameRadius
import LocalCertification.Quantum.FiniteWeightBounds
import LocalCertification.Quantum.WeylWeightEstimates
import CertificationGaussian.IncidentHolderContractions
import CertificationGaussian.FiniteWickInclusionExclusionBounds

/-! # Main results of the manuscript

The main budget results optimize over genuine local product POVMs on arbitrary
measurable outcome spaces. Their proofs instantiate actual Haar target measures,
Born laws, classical randomization, adaptive histories, almost-sure termination,
extended expected costs and deterministic caps on every legal path.

Stable semantic names are followed by navigation aliases for Theorem 1,
Corollary 2, Theorem 3 and the relevant supplemental results. The canonical
sphere and actual unitary-Haar formulations are connected by a proved orbit
map. A supplied complete MUB remains a conditional readout realization.
-/

namespace LocalCertification.Paper

alias tolerance_hierarchy := Protocol.MeasurableExecution.ProductBudget.product_budget_same_event_confidence_hierarchy
alias tolerance_testing_bounds := Protocol.MeasurableExecution.ProductBudget.product_budget_sphere_hierarchy
alias tolerance_haar_bounds := Protocol.MeasurableExecution.ProductBudget.product_budget_haar_hierarchy
alias near_critical_transition := Protocol.MeasurableExecution.qudit_nearCritical_product_confidence_hierarchy
alias near_critical_testing_bounds := Protocol.MeasurableExecution.qudit_nearCritical_product_hierarchy
/-- Fixed-confidence specialization of the moving-threshold bounds. -/
alias near_critical_neighborhood := Protocol.MeasurableExecution.qudit_nearCritical_product_neighborhood
alias near_critical_window := Protocol.MeasurableExecution.qudit_nearCritical_product_hierarchy_uniform
alias near_critical_window_confidence := Protocol.MeasurableExecution.qudit_nearCritical_product_confidence_uniform
alias sharp_decay_and_inversion := Asymptotic.EulerMoments.sharp_order_and_inversion
alias fixed_block_hierarchy := Protocol.MeasurableExecution.FixedBlock.fixedBlock_budget_same_event_confidence_hierarchy
alias fixed_block_testing_bounds := Protocol.MeasurableExecution.FixedBlock.fixedBlock_budget_sphere_hierarchy
alias fixed_block_threshold := Protocol.MeasurableExecution.FixedBlock.fixedBlock_budget_same_event_criterion

/-- The paper's live history-dependent global product kernels compile to the
actual executor with equality of laws, decisions, times and legal paths. -/
alias history_model_compilation := Protocol.MeasurableExecution.PaperHistoryProduct.exists_compile
/-- Both independently defined optimization models have exactly equal
extended expected budgets and every-legal-path maximum budgets. -/
alias history_budget_equivalence := Protocol.MeasurableExecution.PaperHistoryBudget.budget_equivalence

alias theorem_1 := tolerance_hierarchy
/-- The same open neighborhood, Haar-typical family and size cutoff work for both
thresholds and every confidence in each fixed range. -/
alias corollary_2 := Protocol.MeasurableExecution.qudit_nearCritical_product_neighborhood_confidence
alias theorem_3 := Manuscript.physical_sharp_order_and_inversion
/-- The repeated-node Wiener derivation of Theorem 3, in the same dimension parameter. -/
alias theorem_3_wiener := Manuscript.physical_wiener_sharp_order_and_inversion

alias S6_even_endpoints := Manuscript.optimizer_endpoints_even
alias S6_odd_endpoints := Manuscript.optimizer_endpoints_odd
alias qubit_quartic := Manuscript.qubit_quartic_exact
alias qubit_table := Manuscript.qubit_critical_values
alias low_degree_values := Manuscript.low_degree_values

alias S7_bound := Extremal.GeometricSeries.gamma_binomial_bound
alias S7_decay := Extremal.GeometricSeries.gamma_tendsto_zero_of_two_lt
alias S8_Haar := Quantum.completeHaarReadout_scorebounds
alias S8_Pauli := Quantum.completePauliReadout_scorebounds
alias S8_Haar_quantitative := Protocol.quantitativeScoreBounds_haar
alias S8_Pauli_quantitative := Protocol.quantitativeScoreBounds_pauli
alias S8_Haar_protocol := Protocol.fixedScore_haar_canonical
alias S8_Pauli_protocol := Protocol.fixedScore_pauli_canonical
alias S11_Haar := CertificationGaussian.haar_local_graph_contraction_via_incident_holder
alias S11_Pauli := CertificationGaussian.pauli_local_graph_contraction_via_incident_holder
alias S11_MUB := CertificationGaussian.completeMUB_local_graph_contraction_via_incident_holder
alias S12_Wick := CertificationGaussian.complexGaussian_four_normal_blocks_finite_inclusion_exclusion
alias S12_Wick_bound := CertificationGaussian.complexGaussian_four_normal_blocks_finite_norm_le
alias S12_Haar := CertificationGaussian.cardinalityHaar_remainder_bound
alias S12_Pauli := CertificationGaussian.cardinalityPauli_remainder_bound
alias S15 := Protocol.fixedScore_completeMUB_canonical
alias S15_quantitative := Protocol.quantitativeScoreBounds_completeMUB
alias S15_protocol_quantitative := Protocol.fixedScore_completeMUB_quantitative
alias S15_basis_upper := Protocol.completeMUB_corollary_three_six
alias S16_kernel_moments := CertificationGaussian.cardinalityProjectorKernel_moments
alias S17 := Quantum.weylShell_complement_readout
alias S18_sphere := CertificationGaussian.productFrame_common_sphere_eventually
alias S18_Haar := CertificationGaussian.productFrame_common_haar_eventually
alias S18_zero_radius := Quantum.pure_product_referenceL2_sq_le_of_frameFamily
alias S19 := Quantum.measurableExponential_hard_states
alias S19_background := Quantum.MeasurablePOVM.calibrated_denominator_floor
alias S20_high_low := Protocol.MeasurableExecution.BornProtocol.information_of_valid_high_low
alias S20_low_high := Protocol.MeasurableExecution.BornProtocol.information_of_valid_low_high
/-- Exact testing-factor bounds on `0 < δ < 1/2`, with exponential typicality;
also supplies the exact-factor form of the paper's S22. -/
alias S21 := tolerance_testing_bounds
/-- S22 in its logarithmic fixed-confidence-cutoff form. For the exact `L_δ`
factor together with exponential typicality, also see `S21` / `tolerance_testing_bounds`. -/
alias S22 := tolerance_hierarchy
alias S22_finite_high_weight_maxima := Quantum.finite_high_weight_maxima
alias S22_weight_estimates := Quantum.weyl_weight_estimates
alias S23 := fixed_block_hierarchy
alias S23_criterion := fixed_block_threshold
alias S25 := Manuscript.blaschke_lower
alias S25_coefficient := Manuscript.blaschke_coefficient_lower
alias S30 := Manuscript.certificate_optimality
alias S31 := Manuscript.certificate_exists
alias S32_termination := Manuscript.certificate_search_terminates
alias S32_correct := Manuscript.certificate_output_correct
alias S33 := Manuscript.low_degree_values
alias global_comparison := Comparisons.global_projector_comparison

end LocalCertification.Paper
