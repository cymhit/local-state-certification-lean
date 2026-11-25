import LocalCertification.Asymptotic.UpperCandidate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped BigOperators Topology ContDiff
open MeasureTheory Set Real

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The positive real denominator on the unit circle. -/
def poissonDenominator (a t : ℝ) : ℝ := 1 - 2 * a * Real.cos t + a ^ 2

def poissonDensity (a t : ℝ) : ℝ := (1 - a ^ 2) / poissonDenominator a t

def poissonDensityDerivative (a t : ℝ) : ℝ :=
  -2 * a * (1 - a ^ 2) * Real.sin t / (poissonDenominator a t) ^ 2

theorem poissonDenominator_bounds (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    (1 - a) ^ 2 ≤ poissonDenominator a t ∧ poissonDenominator a t ≤ (1 + a) ^ 2 := by
  unfold poissonDenominator
  constructor
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr (Real.cos_le_one t))]
  · have hcos : 0 ≤ Real.cos t + 1 := by linarith [Real.neg_one_le_cos t]
    nlinarith [mul_nonneg ha hcos]

theorem poissonDenominator_pos (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    0 < poissonDenominator a t := by
  have h := (poissonDenominator_bounds a ha0 t).1
  have hs : 0 < (1 - a) ^ 2 := sq_pos_of_pos (by linarith)
  linarith

theorem poissonDenominator_contDiff (a : ℝ) : ContDiff ℝ ∞ (poissonDenominator a) := by
  unfold poissonDenominator
  fun_prop

theorem poissonDenominator_hasDerivAt (a t : ℝ) :
    HasDerivAt (poissonDenominator a) (2 * a * Real.sin t) t := by
  have h := ((hasDerivAt_const t (1 : ℝ)).sub ((Real.hasDerivAt_cos t).const_mul (2 * a))).add_const (a ^ 2)
  convert h using 1
  · funext x; unfold poissonDenominator; simp only [Pi.sub_apply]
  · ring

theorem poissonDensity_contDiff (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ContDiff ℝ ∞ (poissonDensity a) := by
  exact contDiff_const.div (poissonDenominator_contDiff a)
    (fun t => (poissonDenominator_pos a ha0 ha1 t).ne')

theorem poissonDensity_hasDerivAt (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    HasDerivAt (poissonDensity a) (poissonDensityDerivative a t) t := by
  have h := (hasDerivAt_const t (1 - a ^ 2)).div (poissonDenominator_hasDerivAt a t)
    (poissonDenominator_pos a ha0 ha1 t).ne'
  convert h using 1
  · rfl
  · unfold poissonDensityDerivative
    ring

/-- A globally smooth real phase with the required initial value, avoiding an argument branch. -/
def realPhase (a t : ℝ) : ℝ := Real.pi + ∫ u in (0 : ℝ)..t, poissonDensity a u

@[simp] theorem realPhase_zero (a : ℝ) : realPhase a 0 = Real.pi := by simp [realPhase]

theorem realPhase_hasDerivAt (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    HasDerivAt (realPhase a) (poissonDensity a t) t := by
  have hc := (poissonDensity_contDiff a ha0 ha1).continuous
  exact (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add Real.pi

theorem realPhase_deriv (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    deriv (realPhase a) = poissonDensity a :=
  funext (fun t => (realPhase_hasDerivAt a ha0 ha1 t).deriv)

theorem realPhase_contDiff (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ContDiff ℝ ∞ (realPhase a) := by
  rw [contDiff_infty_iff_deriv, realPhase_deriv a ha0 ha1]
  exact ⟨fun t => (realPhase_hasDerivAt a ha0 ha1 t).differentiableAt,
    poissonDensity_contDiff a ha0 ha1⟩

theorem realPhase_second_deriv (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    deriv (deriv (realPhase a)) t = poissonDensityDerivative a t := by
  rw [realPhase_deriv a ha0 ha1]
  exact (poissonDensity_hasDerivAt a ha0 ha1 t).deriv

end LocalCertification.Asymptotic
