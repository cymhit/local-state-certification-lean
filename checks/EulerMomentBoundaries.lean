import Lean
import LocalCertification.Asymptotic.EulerMomentAsymptotics
open scoped BigOperators Topology
open LocalCertification.Asymptotic

example : HasSum (fun n : ℕ => (n : ℝ)^0 * blaschkeCoeff ((3/2 : ℝ)⁻¹) 1 n * ((3/2 : ℝ)⁻¹)^n) 0 := by
  exact LocalCertification.Asymptotic.EulerMoments.blaschkeCoeff_hasSum_root_moment _ (by norm_num) 1 0 (by omega)
example : HasSum (fun n : ℕ => (n : ℝ)^1 * blaschkeCoeff ((3/2 : ℝ)⁻¹) 2 n * ((3/2 : ℝ)⁻¹)^n) 0 := by
  exact LocalCertification.Asymptotic.EulerMoments.blaschkeCoeff_hasSum_root_moment _ (by norm_num) 2 1 (by omega)
example : HasSum (fun n : ℕ => (n : ℝ)^0 * blaschkeCoeff (3 : ℝ)⁻¹ 1 n * ((3 : ℝ)⁻¹)^n) 0 := by
  exact LocalCertification.Asymptotic.EulerMoments.blaschkeCoeff_hasSum_root_moment _ (by norm_num) 1 0 (by omega)
example : HasSum (fun n : ℕ => (n : ℝ)^1 * blaschkeCoeff (3 : ℝ)⁻¹ 2 n * ((3 : ℝ)⁻¹)^n) 0 := by
  exact LocalCertification.Asymptotic.EulerMoments.blaschkeCoeff_hasSum_root_moment _ (by norm_num) 2 1 (by omega)
example (q : ℝ) (hq : 1 < q) :
    2 * q⁻¹ / (1 + blaschkeCoefficientConstant q) ≤ LocalCertification.Extremal.gamma q 0 := by
  simpa using LocalCertification.Asymptotic.EulerMoments.gamma_blaschke_lower q hq 0
example (q : ℝ) (hq : 1 < q) :
    lowerRateConstant q * (q⁻¹)^2 / Real.sqrt 2 ≤ LocalCertification.Extremal.gamma q 2 ∧
    LocalCertification.Extremal.gamma q 2 ≤ upperRateConstant q * (q⁻¹)^2 / Real.sqrt 2 := by
  simpa using LocalCertification.Asymptotic.EulerMoments.gamma_sharp_rate q hq 2 (by omega)
example (q : ℝ) (hq : 1 < q) (j : ℕ) :
    criticalDegree q (LocalCertification.Extremal.gamma q j) = j+1 :=
  criticalDegree_at_critical_value q hq j
#check LocalCertification.Asymptotic.sharp_order_and_inversion
#check LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion

open Lean Elab Command in
run_elab do
  logInfo "REGRESSION_CHECK\tEulerMomentBoundaries\tPASS"
