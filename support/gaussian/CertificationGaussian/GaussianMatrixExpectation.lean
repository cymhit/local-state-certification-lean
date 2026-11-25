import CertificationGaussian.GaussianMatrixOperatorMoments

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators ENNReal
namespace CertificationGaussian
variable {I N : Type*} [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]

omit [DecidableEq I] in
/-- Probability-space Lp monotonicity for the actual operator norm. -/
theorem gaussianMatrixSeries_expectation_le_moment_root (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) {p : Nat} (hp : 0 < p) :
    ∫ x, ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixSeries H x)‖ ∂realGaussianProduct I ≤
      (∫ x, ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixSeries H x)‖^(2*p)
        ∂realGaussianProduct I)^((2*p:Nat):ℝ)⁻¹ := by
  let f := fun x : I → ℝ => ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixSeries H x)‖
  have h1 := gaussianMatrixSeries_opNorm_memLp H hH 1 (by simp)
  have hq := gaussianMatrixSeries_opNorm_memLp H hH (2*p:Nat) (by finiteness)
  have h := eLpNorm_le_eLpNorm_of_exponent_le (f := f) (μ := realGaussianProduct I)
    (show (1:ℝ≥0∞) ≤ (2*p:Nat) by exact_mod_cast (by omega : 1 ≤ 2*p))
  rw [h1.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hq.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast (by omega : 2*p ≠ 0)) (by finiteness)] at h
  simp only [norm_norm, ENNReal.toReal_one, inv_one, Real.rpow_one,
    ENNReal.toReal_natCast, Real.rpow_natCast] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- All positive even degrees yield a quantitative first operator-norm moment estimate. -/
theorem gaussianMatrixSeries_expectation_bound_root (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) {p : Nat} (hp : 0 < p) :
    ∫ x, ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixSeries H x)‖ ∂realGaussianProduct I ≤
      ((Fintype.card N:ℝ)*(2*p:Nat)^p *
        ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖^p)^((2*p:Nat):ℝ)⁻¹ := by
  have hi := gaussianMatrixSeries_opNorm_even_integrable H hH (k := 2*p)
    (by omega) (even_two.mul_right p)
  have ht : Integrable (fun x => (Matrix.trace ((gaussianMatrixSeries H x)^(2*p))).re)
      (realGaussianProduct I) := (gaussianMatrixSeries_trace_power_integrable H (2*p)).re
  have hm := (integral_mono hi ht (fun x => hermitian_opNorm_even_power_le_trace _
    (gaussianMatrixSeries_isHermitian H hH x) (by omega) (even_two.mul_right p))).trans
    (gaussianTraceMoment_bound_pow H hH p)
  exact (gaussianMatrixSeries_expectation_le_moment_root H hH hp).trans
    (Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) hm (by positivity))

/-- Taking the even root removes the covariance power without requiring it to be positive. -/
theorem even_root_pow (b : ℝ) (hb : 0 ≤ b) {p : Nat} (hp : 0 < p) :
    (b^p)^((2*p:Nat):ℝ)⁻¹ = Real.sqrt b := by
  rw [← Real.rpow_natCast b p, ← Real.rpow_mul hb, Real.sqrt_eq_rpow]
  congr 1
  push_cast
  field_simp

/-- Explicit finite-p first moment bound, still with arbitrary finite dimensions. -/
theorem gaussianMatrixSeries_expectation_bound_p (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) {p : Nat} (hp : 0 < p) :
    ∫ x, ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixSeries H x)‖ ∂realGaussianProduct I ≤
      (Fintype.card N:ℝ)^((2*p:Nat):ℝ)⁻¹ * Real.sqrt (2*p:Nat) *
        Real.sqrt ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖ := by
  have h := gaussianMatrixSeries_expectation_bound_root H hH hp
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    even_root_pow _ (by positivity) hp, even_root_pow _ (by positivity) hp] at h
  exact h

/-- A universal numerical constant; it is independent of matrix dimension and coefficient family. -/
def gaussianMatrixExpectationConstant : ℝ :=
  Real.exp (1/2) * Real.sqrt (2*(1+(Real.log 2)⁻¹))

theorem gaussianMatrixExpectationConstant_pos : 0 < gaussianMatrixExpectationConstant := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold gaussianMatrixExpectationConstant
  positivity

/-- Choosing the moment order by the logarithm of dimension gives a universal square-root-log factor. -/
theorem gaussian_matrix_log_moment_choice (n : Nat) (hn : 0 < n) :
    ∃ p : Nat, 0 < p ∧ (n:ℝ)^((2*p:Nat):ℝ)⁻¹ * Real.sqrt (2*p:Nat) ≤
      gaussianMatrixExpectationConstant * Real.sqrt (Real.log (2*(n:ℝ))) := by
  let L : ℝ := Real.log (2*(n:ℝ))
  let p : Nat := Nat.ceil L
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hpL : L ≤ (p:ℝ) := Nat.le_ceil L
  have hp : 0 < p := by exact_mod_cast (lt_of_lt_of_le hL hpL)
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hpU : (p:ℝ) ≤ L+1 := (Nat.ceil_lt_add_one hL.le).le
  have hratio : 1 ≤ L / Real.log 2 := (le_div_iff₀ h2).mpr (by simpa using hL2)
  have hcoef : (p:ℝ) ≤ (1+(Real.log 2)⁻¹)*L := by
    rw [div_eq_mul_inv] at hratio
    calc
      _ ≤ L+1 := hpU
      _ ≤ L+L*(Real.log 2)⁻¹ := by linarith
      _ = _ := by ring
  have hlogn : Real.log (n:ℝ) ≤ L := Real.log_le_log (by positivity) (by nlinarith)
  have hroot : (n:ℝ)^((2*p:Nat):ℝ)⁻¹ ≤ Real.exp (1/2) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    push_cast
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hsqrt : Real.sqrt (2*p:Nat) ≤ Real.sqrt (2*(1+(Real.log 2)⁻¹))*Real.sqrt L := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith
  refine ⟨p, hp, ?_⟩
  calc
    _ ≤ Real.exp (1/2)*(Real.sqrt (2*(1+(Real.log 2)⁻¹))*Real.sqrt L) :=
      mul_le_mul hroot hsqrt (Real.sqrt_nonneg _) (Real.exp_pos _).le
    _ = _ := by unfold gaussianMatrixExpectationConstant; dsimp [L]; ring

/-- First-order Hermitian Gaussian matrix inequality in the genuine Euclidean operator norm.
The same explicit universal constant applies to every finite dimension, including the empty case. -/
theorem gaussianMatrixSeries_expectation_bound (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) :
    ∫ x, ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixSeries H x)‖ ∂realGaussianProduct I ≤
      gaussianMatrixExpectationConstant * Real.sqrt (Real.log (2*(Fintype.card N:ℝ))) *
        Real.sqrt ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖ := by
  cases isEmpty_or_nonempty N with
  | inl hN =>
    let := hN
    have hz (x : I → ℝ) : gaussianMatrixSeries H x = 0 := Subsingleton.elim _ _
    simp [hz]
  | inr hN =>
    let := hN
    obtain ⟨p, hp, hlog⟩ := gaussian_matrix_log_moment_choice (Fintype.card N) Fintype.card_pos
    exact (gaussianMatrixSeries_expectation_bound_p H hH hp).trans
      (mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg _))

end CertificationGaussian
