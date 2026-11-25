import LocalCertification.Protocol.UniformConfidenceHierarchy
import LocalCertification.Comparisons.GlobalProjectorTest
import LocalCertification.Extremal.GeometricSeriesDecay
import CertificationGaussian.RadialBinomialEntropy
import CertificationGaussian.Consumers.HaarSpherePacking
import Lean

open Lean Elab Command
private def releaseRouteRecord (root : String) (passed : Bool)
    (required forbidden : List String) : String :=
  "ROUTE_CHECK\t" ++ (Json.mkObj [("id",toJson root),("passed",toJson passed),
    ("required",toJson required),("forbidden",toJson forbidden),
    ("required_count",toJson required.length),("forbidden_count",toJson forbidden.length)]).compress



open Lean Elab Command
set_option maxHeartbeats 12000000

run_cmd do
  let env ← getEnv
  let cases : Array (String × Array String × Array String) := #[
    ("LocalCertification.Quantum.qudit_haar_product_basis_score_bound", #[
      "CertificationGaussian.separated_card_le_ball_volume_ratio",
      "CertificationGaussian.unitaryFrobenius_real_dimension",
      "CertificationGaussian.tensorUnitaryMatrix_operator_close_of_local_operator",
      "CertificationGaussian.basisProbability_l1_difference_bound",
      "CertificationGaussian.sphereScore_lipschitz_via_l1",
      "CertificationGaussian.kernelPackingMesh_transfer_scale",
      "CertificationGaussian.all_product_score_bound_quartic_radius",
      "CertificationGaussian.Consumers.actual_net_and_radius_package_via_frobenius_packing"],
      #["CertificationGaussian.Consumers.uniform_haar_orbit_processed_probability"]),
    ("LocalCertification.Protocol.qudit_same_event_continuous_confidence_hierarchy", #[
      "LocalCertification.Information.continuousConfidenceRatio_positive_minimum",
      "LocalCertification.Information.inv_log_continuousAt_zero",
      "LocalCertification.Protocol.qudit_exponential_testing_hierarchy_via_product_density",
      "LocalCertification.Protocol.calibrated_terminal_information_finite_via_product_density",
      "LocalCertification.Protocol.terminal_klDiv_finite_via_product_density",
      "LocalCertification.Information.prefixLaw_stopped_klDiv_le_product_density",
      "LocalCertification.Quantum.qudit_haar_product_basis_score_bound",
      "CertificationGaussian.radialLinearLow_gram_factor_eventually",
      "CertificationGaussian.radialLinearFirstLow_mean_eventually",
      "CertificationGaussian.radialLinearFirstHigh_bell_partialTranspose_eventually",
      "CertificationGaussian.weighted_binomial_floor_entropy_bound_termwise"],
      #["LocalCertification.Protocol.qudit_exponential_testing_hierarchy",
        "LocalCertification.Protocol.execution_klDiv_le_truncated_cost"]),
    ("LocalCertification.Comparisons.global_projector_comparison", #[
      "LocalCertification.Comparisons.globalProjector_prob_true",
      "LocalCertification.Comparisons.globalProjector_integral",
      "LocalCertification.Comparisons.iid_bounded_upper_tail",
      "LocalCertification.Comparisons.iid_bounded_lower_tail",
      "LocalCertification.Comparisons.globalProjectorCopies_rounding",
      "LocalCertification.Comparisons.globalProjectorCopies_upper"], #[]),
    ("CertificationGaussian.radialLinearLowLabels_polynomial_ratio_via_binomial_entropy", #[
      "CertificationGaussian.choose_le_exp_binEntropy",
      "CertificationGaussian.hasDerivAt_weightedEntropy",
      "CertificationGaussian.weightedEntropy_strictMonoOn",
      "CertificationGaussian.weighted_binomial_floor_entropy_bound_termwise",
      "CertificationGaussian.radialLinearLowLabels_card"],
      #["CertificationGaussian.weighted_binomial_floor_entropy_bound"]),
    ("LocalCertification.Extremal.GeometricSeries.gamma_tendsto_zero_of_two_lt", #[
      "LocalCertification.Extremal.GeometricSeries.geometric_derivative_norm_bound",
      "LocalCertification.Extremal.GeometricSeries.geometric_derivative_summable_bound",
      "LocalCertification.Extremal.GeometricSeries.geometric_iteratedDeriv_eq_tsum",
      "LocalCertification.Extremal.GeometricSeries.geometric_iteratedDeriv_value",
      "LocalCertification.Extremal.GeometricSeries.hasSum_choose_mul_geometric_via_derivatives",
      "LocalCertification.Extremal.GeometricSeries.weighted_choose_le_geometric",
      "LocalCertification.Extremal.decayPolynomial_admissible"],
      #["LocalCertification.Extremal.gamma_binomial_bound",
        "LocalCertification.Extremal.gamma_tendsto_zero_of_two_lt",
        "hasSum_choose_mul_geometric_of_norm_lt_one"])]
  for (root, required, forbidden) in cases do
    let rn := root.toName
    unless env.contains rn do throwError "Unknown review root: {root}"
    let mut todo := #[rn]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if !seen.contains n then
        seen := seen.insert n
        if let some info := env.find? n then
          todo := todo ++ info.type.getUsedConstants
          if let some v := info.value? (allowOpaque := true) then
            todo := todo ++ v.getUsedConstants
    for name in required do
      unless env.contains name.toName do throwError "Unknown required declaration: {name}"
      unless seen.contains name.toName do throwError "Missing required dependency of {root}: {name}"
      logInfo m!"PRESENT {root} -> {name}"
    for name in forbidden do
      unless env.contains name.toName do throwError "Unknown forbidden declaration: {name}"
      if seen.contains name.toName then throwError "Old endpoint reused by {root}: {name}"
      logInfo m!"ABSENT {root} -> {name}"
    logInfo m!"REVIEW ROUTE PASS: {root}"
    logInfo (releaseRouteRecord root true required.toList forbidden.toList)


example : LocalCertification.Information.continuousConfidenceRatio 0 = 1 := LocalCertification.Information.continuousConfidenceRatio_zero
example (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    HasSum (fun n : ℕ => (((n + 0).choose 0 : ℕ) : ℝ) * z ^ n) (1 / (1 - z) ^ (0 + 1)) :=
  LocalCertification.Extremal.GeometricSeries.hasSum_choose_mul_geometric_via_derivatives 0 z hz hz1
example (n : ℕ) (hn : 0 < n) :
    (n.choose 0 : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy ((0 : ℝ) / n)) :=
  by simpa only [Nat.cast_zero] using CertificationGaussian.choose_le_exp_binEntropy n 0 hn (Nat.zero_le n)
example (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) (hh : ε < 1 / 2) :
    (∑ k ∈ Finset.range (Nat.floor (ε * (0 : ℝ)) + 1), ((0 : ℕ).choose k : ℝ) * M ^ k) ≤
      ((0 : ℝ) + 1) * Real.exp ((0 : ℝ) * (Real.binEntropy ε + ε * Real.log M)) :=
  by simpa only [Nat.cast_zero] using CertificationGaussian.weighted_binomial_floor_entropy_bound_termwise 0 M ε hM hε hh
-- Recover the literal paper generating sum, including z^(r+1), from the implemented shifted HasSum.
example (r : ℕ) (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    HasSum (fun k : ℕ => (k.choose r : ℝ) * z ^ (k+1))
      (z ^ (r+1) / (1-z) ^ (r+1)) := by
  have hs := (LocalCertification.Extremal.GeometricSeries.hasSum_choose_mul_geometric_via_derivatives r z hz hz1).mul_left (z^(r+1))
  have hpre : (∑ k ∈ Finset.range r, (k.choose r : ℝ) * z^(k+1)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk), Nat.cast_zero, zero_mul]
  apply (hasSum_nat_add_iff' (f := fun k : ℕ => (k.choose r : ℝ) * z^(k+1)) r).mp
  rw [hpre, sub_zero]
  convert hs using 1
  · funext k
    rw [show k+r+1=(r+1)+k by omega, pow_add]
    ring
  · ring