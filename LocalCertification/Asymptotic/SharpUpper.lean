import LocalCertification.Asymptotic.CoefficientUpper

open scoped Topology
open Polynomial Set Real

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The original envelope fraction is at most twice any uniform absolute bound. -/
theorem envelopeRatio_le_twice_absolute_bound (q : ℝ) (hq : 1 < q) (p : ℝ[X])
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ k, |LocalCertification.Extremal.weightedValue q p k| ≤ M) :
    LocalCertification.Extremal.envelopeRatio q p ≤ 2 * M := by
  have hl : -M ≤ LocalCertification.Extremal.lowerEnvelope q p := by
    apply le_csInf (Set.range_nonempty _)
    rintro t ⟨k, rfl⟩
    exact (abs_le.mp (hb k)).1
  have hu : LocalCertification.Extremal.upperEnvelope q p ≤ M := by
    apply csSup_le (Set.range_nonempty _)
    rintro t ⟨k, rfl⟩
    exact (abs_le.mp (hb k)).2
  have hz := (LocalCertification.Extremal.envelope_zero_bounds q hq p).1
  rw [LocalCertification.Extremal.envelopeRatio]
  apply (div_le_iff₀ (LocalCertification.Extremal.envelope_denominator_pos q hq p)).mpr
  nlinarith [mul_nonneg hM (neg_nonneg.mpr hz)]

theorem upperNormalizedPolynomial_weighted (q : ℝ) (r k : ℕ) :
    LocalCertification.Extremal.weightedValue q (upperNormalizedPolynomial q⁻¹ r) k =
      upperCoefficient q⁻¹ r (k + 1) / (upperPolynomial q⁻¹ r).eval 0 := by
  rw [LocalCertification.Extremal.weightedValue, upperNormalizedPolynomial, Polynomial.eval_smul,
    upperCoefficient_positive]
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- The actual upper candidate bounds the original envelope infimum, for every real q>1. -/
theorem gamma_sharp_upper (q : ℝ) (hq : 1 < q) (r : ℕ) (hr : 2 ≤ r) :
    LocalCertification.Extremal.gamma q r ≤
      2 * upperOscillationConstant q⁻¹ /
        (Real.sqrt ((r : ℝ) - 1) * (q ^ (r + 1) + (q⁻¹) ^ (r - 1))) := by
  have hq0 : 0 < q := by linarith
  have ha0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have ha1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).mpr hq
  have hs : 0 < Real.sqrt ((r : ℝ) - 1) := Real.sqrt_pos.2 (by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith)
  have hp0 := upperPolynomial_eval_zero_pos q⁻¹ ha0 r (by omega)
  have hK := upperOscillationConstant_pos q⁻¹ ha0 ha1
  have hg : LocalCertification.Extremal.gamma q r ≤ LocalCertification.Extremal.envelopeRatio q (upperNormalizedPolynomial q⁻¹ r) :=
    csInf_le (LocalCertification.Extremal.envelope_ratios_bddBelow q hq r)
      ⟨upperNormalizedPolynomial q⁻¹ r, upperNormalizedPolynomial_admissible q⁻¹ ha0 r (by omega), rfl⟩
  have hbound : ∀ k, |LocalCertification.Extremal.weightedValue q (upperNormalizedPolynomial q⁻¹ r) k| ≤
      (upperOscillationConstant q⁻¹ / Real.sqrt ((r : ℝ) - 1)) / (upperPolynomial q⁻¹ r).eval 0 := by
    intro k
    rw [upperNormalizedPolynomial_weighted, abs_div, abs_of_pos hp0]
    exact div_le_div_of_nonneg_right (upperCoefficient_bound q⁻¹ ha0 ha1 r hr (k + 1)) hp0.le
  have h := hg.trans (envelopeRatio_le_twice_absolute_bound q hq _ _ (by positivity) hbound)
  have he : (upperPolynomial q⁻¹ r).eval 0 = q ^ (r + 1) + (q⁻¹) ^ (r - 1) := by
    rw [upperPolynomial_eval_zero q⁻¹ ha0.ne' r (by omega)]
    simp only [inv_pow, inv_inv]
    ring
  rw [he] at h
  simpa only [div_div, mul_div_assoc] using h

end LocalCertification.Asymptotic
