import LocalCertification.Asymptotic.WienerDuality
import LocalCertification.Extremal.GeometricSeriesDerivatives
import Mathlib.Combinatorics.Enumerative.Stirling

/-! # Repeated-node constraints for absolutely convergent Wiener series -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Metric Set Filter Polynomial
open scoped BigOperators Topology
noncomputable section
namespace LocalCertification.Asymptotic.Wiener

def series (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, c n * z ^ n

private theorem monomial_derivative (c : ℂ) (n k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun t : ℂ => c * t ^ n) z = c * (n.descFactorial k : ℂ) * z ^ (n - k) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  ring

/-- The ordinary complex derivative of the full Wiener series is computed termwise
at every point of the open unit disk. No moment condition is assumed. -/
theorem derivative_hasSum (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖))
    (k : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n => c n * (n.descFactorial k : ℂ) * z ^ (n - k))
      (iteratedDeriv k (series c) z) := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz
  have hR := (norm_nonneg z).trans_lt hzR
  let U := ball (0 : ℂ) R
  let term := fun (n : ℕ) (t : ℂ) => c n * t ^ n
  let M := ∑' n, ‖c n‖
  have hb (n : ℕ) : ‖c n‖ ≤ M := hc.le_tsum n (fun _ _ => norm_nonneg _)
  have major (j : ℕ) := (Extremal.GeometricSeries.geometric_derivative_summable_bound
    j R hR hR1).mul_left M
  have bound (n j : ℕ) (w : ℂ) (hw : w ∈ U) :
      ‖iteratedDeriv j (term n) w‖ ≤ M * ((R ^ j)⁻¹ * ((n : ℝ) ^ j * R ^ n)) := by
    have hwR : ‖w‖ < R := by simpa [U] using hw
    have h := Extremal.GeometricSeries.geometric_derivative_norm_bound n j R hR
      ‖w‖ (by simpa using hwR.le)
    rw [iteratedDeriv_pow, norm_mul, norm_pow] at h
    simp only [Real.norm_natCast, norm_norm] at h
    change ‖iteratedDeriv j (fun t : ℂ => c n * t ^ n) w‖ ≤ _
    rw [monomial_derivative, norm_mul, norm_mul, Complex.norm_natCast, norm_pow, mul_assoc]
    exact mul_le_mul (hb n) h (by positivity) (tsum_nonneg (fun _ => norm_nonneg _))
  have op : IsOpen U := isOpen_ball
  have hzur : z ∈ U := by simpa [U] using hzR
  have within (j n : ℕ) (w : ℂ) (hw : w ∈ U) :
      iteratedDerivWithin j (term n) U w = iteratedDeriv j (term n) w :=
    iteratedDerivWithin_of_isOpen op hw
  have derivative_summable (j : ℕ) (w : ℂ) (hw : w ∈ U) :
      Summable (fun n => iteratedDeriv j (term n) w) :=
    Summable.of_norm_bounded (major j) (fun n => bound n j w hw)
  have hsum (w : ℂ) (hw : w ∈ U) : Summable (fun n => term n w) := by
    simpa only [iteratedDeriv_zero] using derivative_summable 0 w hw
  have hunif (j : ℕ) : SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin j (term n) U) U := by
    have hu : HasSumUniformlyOn (fun n => iteratedDerivWithin j (term n) U)
        (fun w => ∑' n, iteratedDerivWithin j (term n) U w) U := by
      apply HasSumUniformlyOn.of_norm_le_summable (major j)
      intro n w hw
      rw [within j n w hw]
      exact bound n j w hw
    exact hu.hasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  have hdiff (n j : ℕ) (w : ℂ) (hw : w ∈ U) :
      DifferentiableAt ℂ (iteratedDerivWithin j (term n) U) w := by
    have hd : DifferentiableAt ℂ (iteratedDeriv j (term n)) w := by
      rw [show iteratedDeriv j (term n) =
        (fun t : ℂ => c n * (n.descFactorial j : ℂ) * t ^ (n - j)) from
          funext (monomial_derivative (c n) n j)]
      fun_prop
    apply hd.congr_of_eventuallyEq
    filter_upwards [op.mem_nhds hw] with t ht
    exact within j n t ht
  have ht := iteratedDerivWithin_tsum k op hzur hsum
    (fun j _ _ => hunif j) (fun n j w _ hw => hdiff n j w hw)
  rw [iteratedDerivWithin_of_isOpen op hzur] at ht
  change iteratedDeriv k (series c) z = _ at ht
  simp_rw [fun n => within k n z hzur] at ht
  rw [ht]
  simpa only [term, monomial_derivative] using (derivative_summable k z hzur).hasSum

/-- The paper's exact constraints on complex coefficients. -/
def Feasible (a : ℝ) (r : ℕ) (c : ℕ → ℂ) : Prop :=
  Summable (fun n => ‖c n‖) ∧ c 0 = (a : ℂ) ^ (r + 1) ∧
    ∀ k ≤ r, iteratedDeriv k (series c) (a : ℂ) = 0

private theorem weighted_factorial_hasSum (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) (k : ℕ) :
    HasSum (fun n => c n * (a : ℂ) ^ n * (n.descFactorial k : ℂ))
      ((a : ℂ) ^ k * iteratedDeriv k (series c) (a : ℂ)) := by
  have hs := (derivative_hasSum c hc k a (by simpa [Complex.norm_real, abs_of_pos ha] using ha1)).mul_left
    ((a : ℂ)^k)
  apply hs.congr_fun
  intro n
  by_cases hk : k ≤ n
  · have ht : (a : ℂ)^k * (a : ℂ)^(n-k) = (a : ℂ)^n := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    linear_combination -c n * (n.descFactorial k : ℂ) * ht
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (lt_of_not_ge hk)]

/-- Repeated zeros are equivalent to moment cancellation for every real polynomial
through degree r, for arbitrary complex Wiener coefficients. -/
theorem derivatives_iff_polynomial_moments (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (r : ℕ) (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    (∀ k ≤ r, iteratedDeriv k (series c) (a : ℂ) = 0) ↔
      ∀ p : ℝ[X], p.natDegree ≤ r →
      HasSum (fun n : ℕ => c n * (a : ℂ) ^ n * Complex.ofReal (p.eval (n : ℝ))) 0 := by
  constructor
  · intro hd
    have hfac (k : ℕ) (hk : k ≤ r) :
        HasSum (fun n => c n * (a : ℂ) ^ n * (n.descFactorial k : ℂ)) 0 := by
      simpa only [hd k hk, mul_zero] using weighted_factorial_hasSum a ha ha1 c hc k
    have hpow (k : ℕ) (hk : k ≤ r) : HasSum (fun n => c n * (a : ℂ) ^ n * (n : ℂ)^k) 0 := by
      have h := hasSum_sum (s := Finset.range (k+1)) (fun j hj =>
        (hfac j (by have := Finset.mem_range.mp hj; omega)).mul_left (Nat.stirlingSecond k j : ℂ))
      simp only [mul_zero, Finset.sum_const_zero] at h
      apply h.congr_fun
      intro n
      have hi : (n : ℂ)^k = ∑ j ∈ Finset.range (k+1), (Nat.stirlingSecond k j : ℂ) * n.descFactorial j := by
        exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n k
      rw [hi, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    intro p hp
    have h := hasSum_sum (s := Finset.range (r + 1)) (fun k hk =>
      (hpow k (by have := Finset.mem_range.mp hk; omega)).mul_left (p.coeff k : ℂ))
    simp only [mul_zero, Finset.sum_const_zero] at h
    apply h.congr_fun
    intro n
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hp (Nat.lt_succ_self r))]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro hm k hk
    have hs := (hm (Extremal.binomialPolynomial k)
      ((Extremal.binomialPolynomial_degree k).trans hk)).mul_left (k.factorial : ℂ)
    simp only [mul_zero, Extremal.binomialPolynomial_eval_nat, Complex.ofReal_natCast] at hs
    have hf := weighted_factorial_hasSum a ha ha1 c hc k
    have he : (a : ℂ) ^ k * iteratedDeriv k (series c) (a : ℂ) = 0 := by
      apply hf.unique
      apply hs.congr_fun
      intro n
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      ring
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by exact_mod_cast ha.ne'))

end LocalCertification.Asymptotic.Wiener
