import LocalCertification.Asymptotic.BoundaryAmplitude
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Real.Pi.Bounds

open scoped Topology ContDiff
open MeasureTheory Set Real

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The smooth reciprocal used across stationary points. -/
def regularizedReciprocal (ρ x : ℝ) : ℝ := x / (x ^ 2 + ρ ^ 2)

def regularizedReciprocalDerivative (ρ x : ℝ) : ℝ :=
  (ρ ^ 2 - x ^ 2) / (x ^ 2 + ρ ^ 2) ^ 2

theorem regularization_denominator_pos (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    0 < x ^ 2 + ρ ^ 2 := by positivity

theorem regularizedReciprocal_abs (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    |regularizedReciprocal ρ x| ≤ 1 / (2 * ρ) := by
  rw [regularizedReciprocal, abs_div, abs_of_pos (regularization_denominator_pos ρ hρ x)]
  rw [div_le_div_iff₀ (regularization_denominator_pos ρ hρ x) (by positivity : 0 < 2 * ρ)]
  nlinarith [sq_nonneg (|x| - ρ), sq_abs x]

theorem regularizedReciprocalDerivative_abs (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    |regularizedReciprocalDerivative ρ x| ≤ 1 / (x ^ 2 + ρ ^ 2) := by
  have hd := regularization_denominator_pos ρ hρ x
  rw [regularizedReciprocalDerivative, abs_div, abs_of_pos (sq_pos_of_pos hd),
    div_le_div_iff₀ (sq_pos_of_pos hd) hd]
  have h : |ρ ^ 2 - x ^ 2| ≤ x ^ 2 + ρ ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg ρ]
  nlinarith [mul_le_mul_of_nonneg_right h hd.le]

theorem regularizedReciprocal_hasDerivAt (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    HasDerivAt (regularizedReciprocal ρ) (regularizedReciprocalDerivative ρ x) x := by
  convert (hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).add_const (ρ ^ 2))
    (regularization_denominator_pos ρ hρ x).ne' using 1
  · rfl
  · unfold regularizedReciprocalDerivative
    simp only [Pi.pow_apply, id_eq]
    ring

theorem regularizedReciprocal_continuous (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (regularizedReciprocal ρ) :=
  continuous_iff_continuousAt.mpr (fun x => (regularizedReciprocal_hasDerivAt ρ hρ x).continuousAt)

theorem regularizedReciprocalDerivative_continuous (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (regularizedReciprocalDerivative ρ) := by
  unfold regularizedReciprocalDerivative
  exact (continuous_const.sub (continuous_id.pow 2)).div
    ((continuous_id.pow 2).add continuous_const |>.pow 2)
    (fun x => pow_ne_zero _ (regularization_denominator_pos ρ hρ x).ne')

theorem arctan_scaled_hasDerivAt {f : ℝ → ℝ} {f' x ρ : ℝ} (hρ : 0 < ρ)
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => Real.arctan (f t / ρ) / ρ) (f' / (f x ^ 2 + ρ ^ 2)) x := by
  convert ((hf.div_const ρ).arctan).div_const ρ using 1
  field_simp
  ring

/-- An interval-only FTC identity; no differentiability outside the interval is assumed. -/
theorem integral_arctan_weight {f f' : ℝ → ℝ} {a b ρ : ℝ}
    (hab : a ≤ b) (hρ : 0 < ρ) (hf : ContinuousOn f (Icc a b))
    (hf' : ContinuousOn f' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) :
    (∫ t in a..b, f' t / (f t ^ 2 + ρ ^ 2)) =
      Real.arctan (f b / ρ) / ρ - Real.arctan (f a / ρ) / ρ := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    ((Real.continuous_arctan.comp_continuousOn (hf.div_const ρ)).div_const ρ)
    (fun t ht => arctan_scaled_hasDerivAt hρ (hd t ht))
  exact (hf'.div ((hf.pow 2).add continuousOn_const)
    (fun t _ => (regularization_denominator_pos ρ hρ (f t)).ne')).intervalIntegrable_of_Icc hab

/-- On a monotone or antitone interval the weighted variation is at most pi/lambda. -/
theorem integral_abs_arctan_weight_le {f f' : ℝ → ℝ} {a b ρ : ℝ}
    (hab : a ≤ b) (hρ : 0 < ρ) (hf : ContinuousOn f (Icc a b))
    (hf' : ContinuousOn f' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hm : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) :
    (∫ t in a..b, |f' t| / (f t ^ 2 + ρ ^ 2)) ≤ Real.pi / ρ := by
  have hi := integral_arctan_weight hab hρ hf hf' hd
  have ha := Real.arctan_mem_Ioo (f a / ρ)
  have hb := Real.arctan_mem_Ioo (f b / ρ)
  rcases hm with hm | hm
  · have he : (∫ t in a..b, |f' t| / (f t ^ 2 + ρ ^ 2)) =
        ∫ t in a..b, f' t / (f t ^ 2 + ρ ^ 2) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro t ht
      have hs := hm.derivWithin_nonneg (x := t)
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), (hd t ht).deriv] at hs
      dsimp only
      rw [abs_of_nonneg hs]
    rw [he, hi, ← sub_div, div_le_div_iff_of_pos_right hρ]
    linarith [ha.1, hb.2]
  · have he : (∫ t in a..b, |f' t| / (f t ^ 2 + ρ ^ 2)) =
        -(∫ t in a..b, f' t / (f t ^ 2 + ρ ^ 2)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro t ht
      have hs := hm.derivWithin_nonpos (x := t)
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), (hd t ht).deriv] at hs
      dsimp only
      rw [abs_of_nonpos hs, neg_div]
    rw [he, hi, neg_sub, ← sub_div, div_le_div_iff_of_pos_right hρ]
    linarith [hb.1, ha.2]

end LocalCertification.Asymptotic
