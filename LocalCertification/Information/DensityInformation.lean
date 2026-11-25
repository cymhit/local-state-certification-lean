import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Relative entropy from a common reference quadratic bound

The actual Radon--Nikodym derivative of two density measures is their ratio.
The nonnegative integral formula for KL and the scalar logarithm inequality
give the chi-square bound, including zero source density. A positive reference
background bounds the denominator and yields the quadratic information estimate
used for calibrated and near-critical hard-state pairs in the manuscript.
-/

set_option autoImplicit false
open MeasureTheory InformationTheory
open scoped ENNReal
noncomputable section

namespace LocalCertification.Information.DensityInformation

variable {Ω : Type*} [MeasurableSpace Ω]

theorem klFun_le_square (x : ℝ) (hx : 0 ≤ x) : klFun x ≤ (x-1)^2 := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    norm_num [klFun_zero]
  · have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hx.le
    rw [klFun_apply]
    nlinarith

/-- The ratio formula is derived from the actual density representations. -/
theorem rnDeriv_toReal_eq_ratio
    (μ P Q : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfpos : ∀ x, 0 ≤ f x) (hgpos : ∀ x, 0 < g x)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (g x))) :
    (fun x => (P.rnDeriv Q x).toReal) =ᵐ[μ] (fun x => f x / g x) := by
  have hleft : P.rnDeriv μ =ᵐ[μ] (fun x => ENNReal.ofReal (f x)) := by
    rw [hP]
    exact Measure.rnDeriv_withDensity μ hf.ennreal_ofReal
  have hright := Measure.rnDeriv_withDensity_right P μ hg.ennreal_ofReal.aemeasurable
    (ae_of_all μ (fun x => (ENNReal.ofReal_pos.mpr (hgpos x)).ne'))
    (ae_of_all μ (fun _ => ENNReal.ofReal_ne_top))
  rw [← hQ] at hright
  filter_upwards [hleft, hright] with x hx hy
  rw [hy, hx, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (hfpos x), ENNReal.toReal_ofReal (hgpos x).le]
  ring

/-- Chi-square controls KL in extended values before any real integrability
assumption is introduced. -/
theorem klDiv_le_reference_chiSquare
    (μ P Q : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfpos : ∀ x, 0 ≤ f x) (hgpos : ∀ x, 0 < g x)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (g x))) :
    klDiv P Q ≤ ∫⁻ x, ENNReal.ofReal ((f x-g x)^2 / g x) ∂μ := by
  have hPμ : P ≪ μ := by rw [hP]; exact withDensity_absolutelyContinuous _ _
  have hμQ : μ ≪ Q := by
    rw [hQ]
    exact withDensity_absolutelyContinuous' hg.ennreal_ofReal.aemeasurable
      (ae_of_all μ (fun x => (ENNReal.ofReal_pos.mpr (hgpos x)).ne'))
  have hratio := rnDeriv_toReal_eq_ratio μ P Q f g hf hg hfpos hgpos hP hQ
  have hint := lintegral_withDensity_eq_lintegral_mul μ hg.ennreal_ofReal
    (g := fun x => ENNReal.ofReal (klFun (P.rnDeriv Q x).toReal))
    (by fun_prop)
  rw [← hQ] at hint
  rw [klDiv_eq_lintegral_klFun_of_ac (hPμ.trans hμQ), hint]
  apply lintegral_mono_ae
  filter_upwards [hratio] with x hx
  change ENNReal.ofReal (g x) * ENNReal.ofReal (klFun (P.rnDeriv Q x).toReal) ≤ _
  rw [hx, ← ENNReal.ofReal_mul (hgpos x).le]
  apply ENNReal.ofReal_le_ofReal
  calc
    g x * klFun (f x / g x) ≤ g x * (f x / g x - 1)^2 :=
      mul_le_mul_of_nonneg_left (klFun_le_square _ (div_nonneg (hfpos x) (hgpos x).le)) (hgpos x).le
    _ = (f x-g x)^2 / g x := by field_simp [(hgpos x).ne']

/-- A positive reference background and an actual reference squared-distance
bound control ordered KL. Boundedness proves integrability, not an extra KL
or concentration hypothesis. -/
theorem klDiv_le_reference_sq
    (μ P Q : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C β : ℝ) (hβ : 0 < β)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ C) (hgb : ∀ x, β ≤ g x ∧ g x ≤ C)
    (hP : P = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (g x))) :
    klDiv P Q ≤ ENNReal.ofReal (β⁻¹ * ∫ x, (f x-g x)^2 ∂μ) := by
  have hgpos : ∀ x, 0 < g x := fun x => hβ.trans_le (hgb x).1
  have hb : ∀ x, |f x-g x| ≤ C := by
    intro x
    exact abs_le.mpr ⟨by linarith [(hfb x).1, (hgb x).2],
      by linarith [(hfb x).2, (hgpos x).le]⟩
  have hi : Integrable (fun x => (f x-g x)^2) μ := by
    apply Integrable.of_bound ((hf.sub hg).pow_const 2).aestronglyMeasurable (C^2)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_abs (f x-g x)).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) (hb x) 2)
  have hbound : (∫⁻ x, ENNReal.ofReal ((f x-g x)^2 / g x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (β⁻¹ * (f x-g x)^2) ∂μ := by
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    simpa only [div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_left (sq_nonneg (f x-g x)) hβ (hgb x).1
  refine (klDiv_le_reference_chiSquare μ P Q f g hf hg (fun x => (hfb x).1) hgpos hP hQ).trans
    (hbound.trans_eq ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul β⁻¹)
    (ae_of_all μ (fun x => mul_nonneg (inv_nonneg.mpr hβ.le) (sq_nonneg _))), integral_const_mul]

end LocalCertification.Information.DensityInformation
