import LocalCertification.Asymptotic.PhaseComplex
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open scoped Topology ContDiff
open Complex Real Set

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

def boundaryAmplitude (a t : ℝ) : ℂ :=
  (1 - circlePoint t ^ 2) / (1 - (a : ℂ) * circlePoint t) ^ 2

def amplitudeConstant (a : ℝ) : ℝ := (1 + a) ^ 2 / (a * (1 - a ^ 2))

theorem amplitudeConstant_pos (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < amplitudeConstant a := by
  have ha2 : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).2 (by rwa [abs_of_pos ha0])
  exact div_pos (sq_pos_of_pos (by linarith)) (mul_pos ha0 (sub_pos.mpr ha2))

theorem boundaryAmplitude_contDiff (a : ℝ) (ha : |a| < 1) :
    ContDiff ℝ ∞ (boundaryAmplitude a) := by
  have hn : ContDiff ℝ ∞ (fun t : ℝ => (1 : ℂ) - circlePoint t ^ 2) :=
    contDiff_const.sub (circlePoint_contDiff.pow 2)
  have hd : ContDiff ℝ ∞ (fun t : ℝ => ((1 : ℂ) - (a : ℂ) * circlePoint t) ^ 2) :=
    (contDiff_const.sub (contDiff_const.mul circlePoint_contDiff)).pow 2
  convert hn.mul (hd.inv (fun t => pow_ne_zero _
    (blaschke_denominator_ne_zero a (circlePoint t) (by simpa [norm_mul] using ha)))) using 1
  funext t
  exact div_eq_mul_inv _ _

theorem circlePoint_sq (t : ℝ) :
    circlePoint t ^ 2 = Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ)) := by
  unfold circlePoint
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem boundaryAmplitude_norm (a t : ℝ) :
    ‖boundaryAmplitude a t‖ = 2 * |Real.sin t| / poissonDenominator a t := by
  unfold boundaryAmplitude
  rw [norm_div, norm_pow, circle_denominator_norm_sq, circlePoint_sq, norm_sub_rev]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [mul_div_cancel_left₀, norm_mul, Real.norm_eq_abs]

theorem poissonDensityDerivative_abs (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    |poissonDensityDerivative a t| =
      2 * a * (1 - a ^ 2) * |Real.sin t| / poissonDenominator a t ^ 2 := by
  have ha2 : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).2 (by rwa [abs_of_nonneg ha0])
  unfold poissonDensityDerivative
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg ha0,
    abs_of_pos (sub_pos.mpr ha2), abs_of_pos (poissonDenominator_pos a ha0 ha1 t)]
  norm_num

theorem boundaryAmplitude_control (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    ‖boundaryAmplitude a t‖ ≤ amplitudeConstant a * |deriv (deriv (realPhase a)) t| := by
  rw [boundaryAmplitude_norm, realPhase_second_deriv a ha0.le ha1,
    poissonDensityDerivative_abs a ha0.le ha1]
  have hd := poissonDenominator_pos a ha0.le ha1 t
  have ha2 : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).2 (by rwa [abs_of_pos ha0])
  have heq : amplitudeConstant a *
      (2 * a * (1 - a ^ 2) * |Real.sin t| / poissonDenominator a t ^ 2) =
      (2 * |Real.sin t| * (1 + a) ^ 2) / poissonDenominator a t ^ 2 := by
    unfold amplitudeConstant
    field_simp [ha0.ne', (sub_pos.mpr ha2).ne']
  rw [heq, div_le_div_iff₀ hd (sq_pos_of_pos hd)]
  nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg (Real.sin t)))
    (sub_nonneg.mpr (poissonDenominator_bounds a ha0.le t).2)]

theorem poissonDensity_antitone_first (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    AntitoneOn (poissonDensity a) (Icc 0 Real.pi) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 Real.pi) (poissonDensity_contDiff a ha0 ha1).continuous.continuousOn
    (fun t _ => (poissonDensity_hasDerivAt a ha0 ha1 t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(poissonDensity_hasDerivAt a ha0 ha1 t).deriv]
  simp only [interior_Icc, mem_Ioo] at ht
  have ha2 : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).2 (by rwa [abs_of_nonneg ha0])
  unfold poissonDensityDerivative
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) ha0)
        (sub_nonneg.mpr ha2.le)) (Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le ht.2.le)) (sq_nonneg _)

theorem poissonDensity_monotone_second (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    MonotoneOn (poissonDensity a) (Icc Real.pi (2 * Real.pi)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc Real.pi (2 * Real.pi)) (poissonDensity_contDiff a ha0 ha1).continuous.continuousOn
    (fun t _ => (poissonDensity_hasDerivAt a ha0 ha1 t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(poissonDensity_hasDerivAt a ha0 ha1 t).deriv]
  simp only [interior_Icc, mem_Ioo] at ht
  have ha2 : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).2 (by rwa [abs_of_nonneg ha0])
  have hs : Real.sin t ≤ 0 := by
    rw [← Real.sin_sub_two_pi t]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  unfold poissonDensityDerivative
  exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos
    (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) ha0)
      (sub_nonneg.mpr ha2.le)) hs) (sq_nonneg _)

theorem realPhase_deriv_half_monotone (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    AntitoneOn (deriv (realPhase a)) (Icc 0 Real.pi) ∧
    MonotoneOn (deriv (realPhase a)) (Icc Real.pi (2 * Real.pi)) := by
  rw [realPhase_deriv a ha0 ha1]
  exact ⟨poissonDensity_antitone_first a ha0 ha1, poissonDensity_monotone_second a ha0 ha1⟩

/-- The actual upper-candidate coefficients have the phase-amplitude boundary representation. -/
theorem upperCoefficient_hasSum_oscillatory (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) :
    HasSum (fun n : ℕ => (upperCoefficient a r n : ℂ) * circlePoint t ^ n)
      (boundaryAmplitude a t *
        Complex.exp (Complex.I * (((r - 1 : ℕ) : ℂ) * (realPhase a t : ℂ)))) := by
  have ha : |a| < 1 := by rwa [abs_of_pos ha0]
  have h := upperCoefficient_hasSum a ha0.ne' r hr (circlePoint t)
    (by simpa [norm_mul] using ha)
  rw [realPhase_lifts_blaschke a ha0.le ha1 t, ← Complex.exp_nat_mul] at h
  convert h using 1
  congr 2
  ring

end LocalCertification.Asymptotic
