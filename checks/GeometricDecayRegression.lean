import LocalCertification.Extremal.GeometricSeriesDecay
import Lean
set_option pp.universes true
set_option pp.proofs false
#check LocalCertification.Extremal.GeometricSeries.geometric_derivative_norm_bound
#check LocalCertification.Extremal.GeometricSeries.geometric_derivative_summable_bound
#check LocalCertification.Extremal.GeometricSeries.geometric_iteratedDeriv_eq_tsum
#check LocalCertification.Extremal.GeometricSeries.geometric_iteratedDeriv_value
#check LocalCertification.Extremal.GeometricSeries.geometric_derivative_hasSum
#check LocalCertification.Extremal.GeometricSeries.hasSum_choose_mul_geometric_via_derivatives
#check LocalCertification.Extremal.GeometricSeries.weighted_choose_le_geometric
#check LocalCertification.Extremal.GeometricSeries.gamma_binomial_bound
#check LocalCertification.Extremal.GeometricSeries.gamma_elementary_decay
#check LocalCertification.Extremal.GeometricSeries.gamma_tendsto_zero_of_two_lt
#check LocalCertification.Extremal.GeometricSeries.exists_finite_degree_for_gap
#print axioms LocalCertification.Extremal.GeometricSeries.geometric_derivative_norm_bound
#print axioms LocalCertification.Extremal.GeometricSeries.geometric_derivative_summable_bound
#print axioms LocalCertification.Extremal.GeometricSeries.geometric_iteratedDeriv_eq_tsum
#print axioms LocalCertification.Extremal.GeometricSeries.geometric_iteratedDeriv_value
#print axioms LocalCertification.Extremal.GeometricSeries.geometric_derivative_hasSum
#print axioms LocalCertification.Extremal.GeometricSeries.hasSum_choose_mul_geometric_via_derivatives
#print axioms LocalCertification.Extremal.GeometricSeries.weighted_choose_le_geometric
#print axioms LocalCertification.Extremal.GeometricSeries.gamma_binomial_bound
#print axioms LocalCertification.Extremal.GeometricSeries.gamma_elementary_decay
#print axioms LocalCertification.Extremal.GeometricSeries.gamma_tendsto_zero_of_two_lt
#print axioms LocalCertification.Extremal.GeometricSeries.exists_finite_degree_for_gap

example : HasSum (fun n : ℕ => ((n + 0).choose 0 : ℝ) * (1 / 2 : ℝ) ^ n)
    (1 / (1 - (1 / 2 : ℝ)) ^ (0 + 1)) :=
  LocalCertification.Extremal.GeometricSeries.hasSum_choose_mul_geometric_via_derivatives 0 (1 / 2) (by norm_num) (by norm_num)
example : LocalCertification.Extremal.gamma (3 / 2) 2 ≤ (((3 / 2 : ℝ) - 1)⁻¹) ^ (2 + 1) :=
  LocalCertification.Extremal.GeometricSeries.gamma_binomial_bound (3 / 2) (by norm_num) 2
example : Filter.Tendsto (LocalCertification.Extremal.gamma 3) Filter.atTop (nhds 0) :=
  LocalCertification.Extremal.GeometricSeries.gamma_tendsto_zero_of_two_lt 3 (by norm_num)
#check LocalCertification.Extremal.gamma_elementary_decay
#check LocalCertification.Extremal.gamma_tendsto_zero_of_two_lt

open Lean Elab Command in
run_cmd do
  let mut seen : NameSet := {}
  let mut todo := [``LocalCertification.Extremal.GeometricSeries.exists_finite_degree_for_gap]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if !seen.contains n then
      seen := seen.insert n
      let ci ← getConstInfo n
      for d in ci.getUsedConstantsAsSet.toArray do
        if (d.toString.splitOn "LocalCertification.").length > 1 then
          todo := d :: todo
  for n in [``LocalCertification.Extremal.GeometricSeries.geometric_iteratedDeriv_eq_tsum,
      ``LocalCertification.Extremal.GeometricSeries.geometric_iteratedDeriv_value,
      ``LocalCertification.Extremal.GeometricSeries.hasSum_choose_mul_geometric_via_derivatives,
      ``LocalCertification.Extremal.GeometricSeries.weighted_choose_le_geometric,
      ``LocalCertification.Extremal.GeometricSeries.gamma_binomial_bound] do
    unless seen.contains n do
      throwError "Missing required proof dependency: {n}"
    logInfo m!"REQUIRED PRESENT {n}"
  for n in [``LocalCertification.Extremal.weighted_choose_le_geometric,
      ``LocalCertification.Extremal.gamma_binomial_bound,
      ``LocalCertification.Extremal.gamma_tendsto_zero_of_two_lt] do
    if seen.contains n then
      throwError "Forbidden old endpoint dependency: {n}"
    logInfo m!"OLD ENDPOINT ABSENT {n}"

open Lean Elab Command in
run_elab do
  logInfo "REGRESSION_CHECK\tGeometricDecayRegression\tPASS"
