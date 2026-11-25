import LocalCertification.Asymptotic.PhaseScalar
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

open scoped BigOperators Topology ContDiff ComplexConjugate
open Complex Real

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

def circlePoint (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

@[simp] theorem circlePoint_norm (t : ℝ) : ‖circlePoint t‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal t

@[simp] theorem circlePoint_zero : circlePoint 0 = 1 := by simp [circlePoint]

theorem circlePoint_ne_zero (t : ℝ) : circlePoint t ≠ 0 := Complex.exp_ne_zero _

theorem circlePoint_hasDerivAt (t : ℝ) :
    HasDerivAt circlePoint (Complex.I * circlePoint t) t := by
  have h := ((hasDerivAt_id t).ofReal_comp.const_mul Complex.I).cexp
  convert h using 1
  · rfl
  · change Complex.I * Complex.exp (Complex.I * (t : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) * (Complex.I * ((1 : ℝ) : ℂ))
    simp only [Complex.ofReal_one, mul_one]
    exact mul_comm _ _

theorem circlePoint_contDiff : ContDiff ℝ ∞ circlePoint := by
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

@[simp] theorem circlePoint_re (t : ℝ) : (circlePoint t).re = Real.cos t := by
  simp [circlePoint, Complex.exp_re]

@[simp] theorem circlePoint_im (t : ℝ) : (circlePoint t).im = Real.sin t := by
  simp [circlePoint, Complex.exp_im]

theorem circle_denominator_norm_sq (a t : ℝ) :
    ‖1 - (a : ℂ) * circlePoint t‖ ^ 2 = poissonDenominator a t := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    circlePoint_re, circlePoint_im]
  unfold poissonDenominator
  have h := congrArg (fun x : ℝ => a ^ 2 * x) (Real.sin_sq_add_cos_sq t)
  nlinarith [h]

theorem circle_denominator_complex (a t : ℝ) :
    (poissonDenominator a t : ℂ) =
      (1 - (a : ℂ) * circlePoint t) * (1 - (a : ℂ) * (circlePoint t)⁻¹) := by
  rw [← circle_denominator_norm_sq, Complex.ofReal_pow, ← Complex.mul_conj']
  rw [map_sub, map_one, map_mul, Complex.conj_ofReal,
    ← Complex.inv_eq_conj (circlePoint_norm t)]

theorem blaschke_circle_hasDerivAt_raw (a : ℝ) (ha : |a| < 1) (t : ℝ) :
    HasDerivAt (fun u : ℝ => blaschke a (circlePoint u))
      (Complex.I * circlePoint t * ((a : ℂ) ^ 2 - 1) /
        (1 - (a : ℂ) * circlePoint t) ^ 2) t := by
  have hden : 1 - (a : ℂ) * circlePoint t ≠ 0 :=
    blaschke_denominator_ne_zero a _ (by simpa [norm_mul] using ha)
  have h := ((hasDerivAt_const t (a : ℂ)).sub (circlePoint_hasDerivAt t)).div
    ((hasDerivAt_const t (1 : ℂ)).sub ((circlePoint_hasDerivAt t).const_mul (a : ℂ))) hden
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply]
    ring

/-- The actual boundary factor satisfies the scalar Poisson phase equation. -/
theorem blaschke_circle_hasDerivAt (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    HasDerivAt (fun u : ℝ => blaschke a (circlePoint u))
      (Complex.I * (poissonDensity a t : ℂ) * blaschke a (circlePoint t)) t := by
  have ha : |a| < 1 := by rwa [abs_of_nonneg ha0]
  convert blaschke_circle_hasDerivAt_raw a ha t using 1
  have hden : 1 - (a : ℂ) * circlePoint t ≠ 0 :=
    blaschke_denominator_ne_zero a _ (by simpa [norm_mul] using ha)
  have hz := circlePoint_ne_zero t
  have hzma : -(a : ℂ) + circlePoint t ≠ 0 := by
    intro hzero
    have he : circlePoint t = (a : ℂ) := by linear_combination hzero
    have hn := circlePoint_norm t
    rw [he, Complex.norm_real, Real.norm_eq_abs] at hn
    linarith
  unfold poissonDensity blaschke
  push_cast
  rw [circle_denominator_complex]
  field_simp [hzma]
  ring_nf
  field_simp [hzma]
  ring

/-- The integral-defined smooth real phase lifts the actual Blaschke boundary function. -/
theorem realPhase_lifts_blaschke (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    blaschke a (circlePoint t) = Complex.exp (Complex.I * (realPhase a t : ℂ)) := by
  let H : ℝ → ℂ := fun u => blaschke a (circlePoint u) *
    Complex.exp (-Complex.I * (realPhase a u : ℂ))
  have hH (u : ℝ) : HasDerivAt H 0 u := by
    have he := ((realPhase_hasDerivAt a ha0 ha1 u).ofReal_comp.const_mul (-Complex.I)).cexp
    have hb := blaschke_circle_hasDerivAt a ha0 ha1 u
    convert hb.mul he using 1
    ring
  have hc : H t = H 0 := is_const_of_deriv_eq_zero
    (fun u => (hH u).differentiableAt) (fun u => (hH u).deriv) t 0
  have hbase : blaschke a 1 = -1 := by
    have hne : (1 : ℂ) - (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr ha1))
    unfold blaschke
    field_simp
    ring
  have hexp : Complex.exp (-Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [neg_mul, Complex.exp_neg]
    have hp : Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I := mul_comm _ _
    rw [hp, Complex.exp_pi_mul_I]
    norm_num
  have ht : blaschke a (circlePoint t) * Complex.exp (-Complex.I * (realPhase a t : ℂ)) = 1 := by
    simpa only [H, circlePoint_zero, realPhase_zero, hbase, hexp, neg_mul_neg, one_mul] using hc
  apply mul_right_cancel₀ (Complex.exp_ne_zero (-Complex.I * (realPhase a t : ℂ)))
  rw [ht, ← Complex.exp_add]
  have hz : Complex.I * (realPhase a t : ℂ) + -Complex.I * (realPhase a t : ℂ) = 0 := by ring
  rw [hz, Complex.exp_zero]

end LocalCertification.Asymptotic
