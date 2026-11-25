import Mathlib.MeasureTheory.Function.L2Space

/-! Common-reference quadratic estimates.  The two functions live in the same
`L²(μ)` space; no change of reference measure is hidden in the mixture bound. -/

open MeasureTheory
open scoped ENNReal

namespace LocalCertification.Information.ReferenceL2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The real square integral is the squared norm of the actual `L²` class. -/
theorem integral_square_eq_norm_sq (μ : Measure Ω) (f : Ω → ℝ)
    (hf : MemLp f 2 μ) : (∫ x, (f x)^2 ∂μ) = ‖hf.toLp f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, Real.norm_eq_abs, sq_abs]

/-- The square root of the second moment is exactly the common-reference norm. -/
theorem sqrt_integral_square_eq_norm (μ : Measure Ω) (f : Ω → ℝ)
    (hf : MemLp f 2 μ) : Real.sqrt (∫ x, (f x)^2 ∂μ) = ‖hf.toLp f‖ := by
  rw [integral_square_eq_norm_sq μ f hf, Real.sqrt_sq (norm_nonneg _)]

/-- Minkowski's inequality for a linear combination against one reference measure. -/
theorem sqrt_integral_square_combination_le (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (a b : ℝ) :
    Real.sqrt (∫ x, (a*f x+b*g x)^2 ∂μ) ≤
      |a| * Real.sqrt (∫ x, (f x)^2 ∂μ) + |b| * Real.sqrt (∫ x, (g x)^2 ∂μ) := by
  have hcomb : MemLp (a • f + b • g) 2 μ := (hf.const_smul a).add (hg.const_smul b)
  change Real.sqrt (∫ x, ((a • f + b • g) x)^2 ∂μ) ≤ _
  rw [sqrt_integral_square_eq_norm μ _ hcomb, sqrt_integral_square_eq_norm μ f hf,
    sqrt_integral_square_eq_norm μ g hg,
    MemLp.toLp_add (hf.const_smul a) (hg.const_smul b),
    MemLp.toLp_const_smul a hf, MemLp.toLp_const_smul b hg]
  simpa only [norm_smul, Real.norm_eq_abs] using
    norm_add_le (a • hf.toLp f) (b • hg.toLp g)

/-- Squaring the common-reference triangle inequality retains the quadratic
dependence on each mixture coefficient. -/
theorem integral_square_combination_le (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (a b : ℝ) :
    (∫ x, (a*f x+b*g x)^2 ∂μ) ≤
      2*a^2*(∫ x, (f x)^2 ∂μ) + 2*b^2*(∫ x, (g x)^2 ∂μ) := by
  have hf0 : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hg0 : 0 ≤ ∫ x, (g x)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hc0 : 0 ≤ ∫ x, (a*f x+b*g x)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    (∫ x, (a*f x+b*g x)^2 ∂μ) =
        (Real.sqrt (∫ x, (a*f x+b*g x)^2 ∂μ))^2 := (Real.sq_sqrt hc0).symm
    _ ≤ (|a| * Real.sqrt (∫ x, (f x)^2 ∂μ) +
        |b| * Real.sqrt (∫ x, (g x)^2 ∂μ))^2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_integral_square_combination_le μ f g hf hg a b) 2
    _ ≤ 2*(|a| * Real.sqrt (∫ x, (f x)^2 ∂μ))^2 +
        2*(|b| * Real.sqrt (∫ x, (g x)^2 ∂μ))^2 := by
      nlinarith [sq_nonneg (|a| * Real.sqrt (∫ x, (f x)^2 ∂μ) -
        |b| * Real.sqrt (∫ x, (g x)^2 ∂μ))]
    _ = _ := by rw [mul_pow, mul_pow, sq_abs, sq_abs,
      Real.sq_sqrt hf0, Real.sq_sqrt hg0]; ring

end LocalCertification.Information.ReferenceL2
