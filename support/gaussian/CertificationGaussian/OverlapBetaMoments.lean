import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The polynomial moments of the beta law for complex-sphere overlaps -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CertificationGaussian

private theorem betaPDFReal_nonnegative (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ betaPDFReal a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 ha hb).le
  · simp [betaPDFReal, hx]

private theorem integral_beta_density (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂betaMeasure a b = ∫ x, betaPDFReal a b x * f x := by
  unfold betaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (betaPDF a b) from (measurable_betaPDFReal a b).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonnegative a b _ ha hb)]

/-- Multiplying the density of Beta(1,b) by the k-th power shifts its first
parameter. The moment is therefore the ratio of the normalizing constants. -/
theorem betaOne_moment (k : ℕ) (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, x ^ k ∂betaMeasure 1 b = beta (k + 1) b / beta 1 b := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  let _ := isProbabilityMeasureBeta hk hb
  have hnorm := integral_beta_density ((k : ℝ) + 1) b hk hb (fun _ => 1)
  simp at hnorm
  rw [integral_beta_density 1 b zero_lt_one hb]
  have h (x : ℝ) : betaPDFReal 1 b x * x ^ k =
      (beta ((k : ℝ) + 1) b / beta 1 b) * betaPDFReal ((k : ℝ) + 1) b x := by
    by_cases hx : 0 < x ∧ x < 1
    · simp only [betaPDFReal, ite_eq_left hx, sub_self, Real.rpow_zero, mul_one, add_sub_cancel_right,
        Real.rpow_natCast]
      field_simp [ne_of_gt (beta_pos hk hb), ne_of_gt (beta_pos zero_lt_one hb)]
    · simp [betaPDFReal, hx]
  simp_rw [h]
  rw [integral_const_mul, ← hnorm, mul_one]

/-- The third beta moment, with b = d−1 for a Haar vector in complex dimension d. -/
theorem betaOne_third_moment (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, x ^ 3 ∂betaMeasure 1 b = 6 / ((b + 1) * (b + 2) * (b + 3)) := by
  rw [betaOne_moment 3 b hb]
  unfold beta
  norm_num [Real.Gamma_nat_eq_factorial]
  have h1 := Real.Gamma_add_one (show b ≠ 0 by positivity)
  have h2 := Real.Gamma_add_one (show b + 1 ≠ 0 by positivity)
  have h3 := Real.Gamma_add_one (show b + 2 ≠ 0 by positivity)
  have h4 := Real.Gamma_add_one (show b + 3 ≠ 0 by positivity)
  rw [show 1 + b = b + 1 by ring, show 4 + b = (b + 3) + 1 by ring, h4,
    show b + 3 = (b + 2) + 1 by ring, h3, show b + 2 = (b + 1) + 1 by ring, h2, h1]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hb)]

end CertificationGaussian

