import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Variational lower bounds for relative entropy

Exponential tilting gives the bounded-test direction of the variational formula
on an arbitrary measurable space. The statement permits infinite relative
entropy and is a foundation for the general-record recursion in Supplemental Material Section V.A.
It does not assert the converse variational formula or the sequential bound.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace LocalCertification.Information

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Log-likelihood ratios change by the log density of an exponential tilt. -/
theorem llr_tilted_right_of_ac
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hμν : μ ≪ ν)
    (he : Integrable (fun x => Real.exp (f x)) ν) :
    llr μ (ν.tilted f) =ᵐ[μ]
      fun x => llr μ ν x - f x + Real.log (∫ x, Real.exp (f x) ∂ν) := by
  have hZ : 0 < ∫ x, Real.exp (f x) ∂ν := integral_exp_pos he
  filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_right μ ν he),
    Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hpos htop
  have hr : (μ.rnDeriv ν x).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' htop.ne).ne'
  simp only [llr, hx]
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hZ).ne' hr,
    Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  ring

/-- Every integrable exponential test gives a lower bound on relative entropy.
No finiteness, countable-generation or standard-Borel condition is imposed on
the outcome space. Infinite relative entropy is handled before real-valued
integral manipulations. -/
theorem klDiv_variational_lower_bound
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Integrable f μ)
    (he : Integrable (fun x => Real.exp (f x)) ν) :
    ENNReal.ofReal ((∫ x, f x ∂μ) - Real.log (∫ x, Real.exp (f x) ∂ν)) ≤
      InformationTheory.klDiv μ ν := by
  by_cases htop : InformationTheory.klDiv μ ν = ∞
  · simp [htop]
  obtain ⟨hμν, hi⟩ := InformationTheory.klDiv_ne_top_iff.mp htop
  let : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted he
  have htilt : μ ≪ ν.tilted f := hμν.trans (absolutelyContinuous_tilted he)
  have hllr := llr_tilted_right_of_ac μ ν f hμν he
  have hitilt : Integrable (llr μ (ν.tilted f)) μ :=
    (integrable_congr hllr).2 ((hi.sub hf).add (integrable_const _))
  have hnonneg : 0 ≤ ∫ x, llr μ (ν.tilted f) x ∂μ := by
    simpa using InformationTheory.integral_llr_add_sub_measure_univ_nonneg htilt hitilt
  rw [integral_congr_ae hllr] at hnonneg
  change 0 ≤ ∫ x, ((llr μ ν - f) x +
    Real.log (∫ y, Real.exp (f y) ∂ν)) ∂μ at hnonneg
  rw [integral_add (hi.sub hf) (integrable_const _)] at hnonneg
  simp only [Pi.sub_apply] at hnonneg
  rw [integral_sub hi hf] at hnonneg
  simp only [integral_const] at hnonneg
  simp at hnonneg
  have hbound : (∫ x, f x ∂μ) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤
      ∫ x, llr μ ν x ∂μ := by linarith
  rw [InformationTheory.klDiv_of_ac_of_integrable hμν hi]
  simpa using ENNReal.ofReal_le_ofReal hbound

end LocalCertification.Information
