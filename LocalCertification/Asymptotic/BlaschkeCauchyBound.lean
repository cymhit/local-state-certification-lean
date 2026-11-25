import LocalCertification.Asymptotic.BlaschkeTermwiseDerivatives
import Mathlib.Analysis.Complex.Liouville

/-! # Cauchy's estimate for the Blaschke coefficients -/

set_option autoImplicit false
open Metric Set Filter
open scoped Topology BigOperators
noncomputable section
namespace LocalCertification.Asymptotic

private theorem blaschke_derivative_at_zero (a : ℝ) (ha : |a| < 1) (s k : ℕ) :
    iteratedDeriv k (fun z => blaschke a z ^ s) 0 =
      (blaschkeCoeff a s k : ℂ) * (k.factorial : ℂ) := by
  obtain ⟨R, T, hR, hRT, hTa⟩ := blaschke_uniform_radii a ha
  rw [blaschke_iteratedDeriv_eq_tsum a s k R T hR.le hRT hTa 0 (mem_ball_self (by linarith))]
  rw [tsum_eq_single k]
  · simp [blaschkeSeriesTerm_iteratedDeriv, Nat.descFactorial_eq_factorial_mul_choose]
  · intro n hn
    rw [blaschkeSeriesTerm_iteratedDeriv]
    rcases lt_or_gt_of_ne hn with h | h
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    · simp [Nat.sub_ne_zero_of_lt h]

/-- A single boundary norm on the circle of radius R controls every Taylor coefficient. -/
theorem blaschke_cauchy_bound (a : ℝ) (ha : |a| < 1) (s : ℕ) (R : ℝ)
    (hR : 1 < R) (hRa : |a| * R < 1) :
    ∃ C : ℝ, ∀ n : ℕ, |blaschkeCoeff a s n| ≤ C / R ^ n := by
  have hr : 0 < R := by linarith
  let f := fun z => blaschke a z ^ s
  have hd (z : ℂ) (hz : ‖z‖ ≤ R) : DifferentiableAt ℂ f z := by
    have h : ‖(a : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hz (abs_nonneg a)).trans_lt hRa
    unfold f blaschke
    fun_prop (disch := exact blaschke_denominator_ne_zero a z h)
  have hf : DiffContOnCl ℂ f (ball 0 R) := by
    constructor
    · intro z hz
      exact (hd z ((show ‖z‖ < R by simpa using hz).le)).differentiableWithinAt
    · intro z hz
      have hz' : z ∈ closedBall (0 : ℂ) R := closure_ball_subset_closedBall hz
      exact (hd z (by simpa using hz')).continuousAt.continuousWithinAt
  have hcontinuity : ContinuousOn (fun z => ‖f z‖) (sphere 0 R) := by
    intro z hz
    exact (hd z ((show ‖z‖ = R by simpa using hz).le)).continuousAt.norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) R).bddAbove_image hcontinuity
  refine ⟨C, fun n => ?_⟩
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf
    (fun z hz => hC ⟨z, hz, rfl⟩)
  change ‖iteratedDeriv n (fun z => blaschke a z ^ s) 0‖ ≤ _ at h
  rw [blaschke_derivative_at_zero a ha, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast] at h
  have hp : (0 : ℝ) < n.factorial := by positivity
  apply le_of_mul_le_mul_right (a := (n.factorial : ℝ)) _ hp
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- Cauchy decay gives a summable majorant for every differentiated series
on the entire closed unit disk. -/
theorem blaschke_cauchy_derivative_series (a : ℝ) (ha : |a| < 1) (s k : ℕ) :
    HasSumUniformlyOn (fun n => iteratedDeriv k (blaschkeSeriesTerm a s n))
      (fun z => ∑' n, iteratedDeriv k (blaschkeSeriesTerm a s n) z) (closedBall 0 1) := by
  obtain ⟨R, T, hR, hRT, hTa⟩ := blaschke_uniform_radii a ha
  have hRa := (mul_le_mul_of_nonneg_left hRT.le (abs_nonneg a)).trans_lt hTa
  obtain ⟨C, hC⟩ := blaschke_cauchy_bound a ha s R hR hRa
  have hi : ‖R⁻¹‖ < 1 := by rw [Real.norm_of_nonneg (by positivity)]; exact inv_lt_one_of_one_lt₀ hR
  have hs := (summable_pow_mul_geometric_of_norm_lt_one k hi).mul_left C
  apply HasSumUniformlyOn.of_norm_le_summable hs
  intro n z hz
  have h := blaschkeSeriesTerm_derivative_norm_le a s n k 1 le_rfl z (by simpa using hz)
  simp only [one_pow, mul_one] at h
  apply h.trans
  have hc := mul_le_mul_of_nonneg_left (hC n) (by positivity : (0 : ℝ) ≤ (n : ℝ)^k)
  simpa only [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using hc

/-- All differentiated series converge uniformly to the actual derivatives on
the closed unit disk, using the Cauchy coefficient majorant. -/
theorem blaschke_cauchy_uniform_derivatives (a : ℝ) (ha : |a| < 1) (s k : ℕ) :
    HasSumUniformlyOn (fun n => iteratedDeriv k (blaschkeSeriesTerm a s n))
      (iteratedDeriv k (fun z => blaschke a z ^ s)) (closedBall 0 1) := by
  apply (blaschke_cauchy_derivative_series a ha s k).congr_right
  intro z hz
  obtain ⟨R, T, hR, hRT, hTa⟩ := blaschke_uniform_radii a ha
  have hzR : z ∈ ball 0 R := by
    simpa using (lt_of_le_of_lt (show ‖z‖ ≤ 1 by simpa using hz) hR)
  exact (blaschke_iteratedDeriv_eq_tsum a s k R T hR.le hRT hTa z hzR).symm

end LocalCertification.Asymptotic
