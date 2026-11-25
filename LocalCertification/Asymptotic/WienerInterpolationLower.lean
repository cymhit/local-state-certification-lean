import LocalCertification.Asymptotic.WienerExtremum
import LocalCertification.Asymptotic.CoefficientUpper

/-! # A lower bound for repeated-node Wiener interpolation

Pair the coefficients of an arbitrary feasible series with a polynomial
moment test. The uniform oscillatory coefficient estimate bounds the
test in the dual supremum norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial
noncomputable section
namespace LocalCertification.Asymptotic.Wiener

private theorem polynomial_test (a : ℝ) (ha : 0 < a) (r : ℕ) (f : ℕ → ℝ)
    (hf : MomentFeasible a r f) (p : ℝ[X]) (hp : p.natDegree ≤ r) (B : ℝ)
    (hB : ∀ n : ℕ, |a ^ (n+1) * p.eval ((n : ℝ)+1)| ≤ B) :
    a^(r+1) * |p.eval 0| ≤ B * tailNorm f := by
  let v := fun n : ℕ => f n * a ^ (n+1) * p.eval ((n : ℝ)+1)
  have hs : HasSum v (-(a^(r+1)) * p.eval 0) := hf.2 p hp
  have habs := hs.summable.norm
  have hb (n : ℕ) : ‖v n‖ ≤ B * |f n| := by
    dsimp only [v]
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB n) (abs_nonneg _)
  have h := (norm_tsum_le_tsum_norm habs).trans
    (habs.tsum_le_tsum hb (hf.1.mul_left B))
  simpa only [hs.tsum_eq, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (pow_pos ha _),
    tsum_mul_left, tailNorm] using h

/-- The fixed-node interpolation lower bound, including multiplicities one and two. -/
theorem szehr_zarouf_lower (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, c * Real.sqrt (r + 1 : ℕ) ≤ phi a r := by
  let K := upperOscillationConstant a
  have hK : 0 < K := upperOscillationConstant_pos a ha ha1
  let c := min (a^2 / 2) (1/(2*K))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc, fun r => ?_⟩
  have hq : 1 < a⁻¹ := (one_lt_inv₀ ha).mpr ha1
  have he := phi_eq_real_moment_infimum a⁻¹ hq r
  simp only [inv_inv] at he
  rw [he]
  obtain ⟨f₀, hf₀, _⟩ := finite_dual_attains a⁻¹ hq r
  simp only [inv_inv] at hf₀
  apply le_csInf (s := tailNorm '' {f | MomentFeasible a r f}) ⟨_, f₀, hf₀, rfl⟩
  rintro _ ⟨f, hf, rfl⟩
  by_cases hr : 2 ≤ r
  · have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    let t := Real.sqrt ((r:ℝ)-1)
    have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have htest := polynomial_test a ha r f hf (upperPolynomial a r) (upperPolynomial_degree a r)
      (K / t) (fun n => by simpa only [upperCoefficient_positive] using upperCoefficient_bound a ha ha1 r hr (n+1))
    rw [abs_of_pos (upperPolynomial_eval_zero_pos a ha r (by omega)),
      upperPolynomial_eval_zero a ha.ne' r (by omega), mul_add,
      mul_inv_cancel₀ (pow_pos ha _).ne'] at htest
    have hminor : 1 ≤ K / t * tailNorm f := by
      linarith [mul_nonneg (pow_pos ha (r+1)).le (pow_pos ha (r-1)).le]
    have hh : t ≤ K * tailNorm f := by
      rw [div_mul_eq_mul_div] at hminor
      simpa only [one_mul] using (le_div_iff₀ ht).mp hminor
    have hsize : Real.sqrt (r + 1 : ℕ) ≤ 2*t := by
      have ht2 := Real.sq_sqrt (by linarith : 0 ≤ (r:ℝ)-1)
      have hs2 := Real.sq_sqrt (by positivity : 0 ≤ ((r+1:ℕ):ℝ))
      push_cast at hs2 ⊢
      dsimp only [t] at *
      nlinarith [Real.sqrt_nonneg ((r : ℝ) + 1)]
    calc
      _ ≤ (1/(2*K)) * Real.sqrt (r + 1 : ℕ) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
      _ ≤ tailNorm f := by
        rw [one_div, ← div_eq_inv_mul]
        apply (div_le_iff₀ (by positivity : 0 < 2*K)).mpr
        linarith
  · have htest := polynomial_test a ha r f hf 1 (Extremal.admissible_one r).1 1 (fun n => by
      simpa only [Polynomial.eval_one, mul_one, abs_of_pos (pow_pos ha _)] using
        (pow_le_one₀ ha.le ha1.le (n := n+1)))
    simp only [Polynomial.eval_one, abs_one, mul_one, one_mul] at htest
    have hle : a^2 ≤ a^(r+1) := pow_le_pow_of_le_one ha.le ha1.le (by omega)
    have hsize : Real.sqrt (r + 1 : ℕ) ≤ 2 :=
      (Real.sqrt_le_left (by norm_num)).mpr (by exact_mod_cast (show r+1 ≤ 2^2 by omega))
    calc
      _ ≤ c * 2 := mul_le_mul_of_nonneg_left hsize hc.le
      _ ≤ a^2 := by have h := min_le_left (a^2/2) (1/(2*K)); change c ≤ _ at h; linarith
      _ ≤ _ := hle.trans htest

end LocalCertification.Asymptotic.Wiener
