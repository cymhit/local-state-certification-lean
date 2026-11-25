import LocalCertification.Asymptotic.OscillatoryCandidate

open scoped BigOperators Topology
open MeasureTheory AddCircle Complex Real

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
namespace LocalCertification.Asymptotic

def upperBoundary {T : ℝ} (a : ℝ) (r : ℕ) (t : AddCircle T) : ℂ :=
  ((1 - fourier 1 t ^ 2) / (1 - (a : ℂ) * fourier 1 t) ^ 2) * blaschke a (fourier 1 t) ^ (r - 1)

theorem upperCoefficient_summable_abs (a : ℝ) (ha0 : a ≠ 0) (ha : |a| < 1)
    (r : ℕ) (hr : 1 ≤ r) : Summable (fun n => |upperCoefficient a r n|) := by
  have hs : Summable (fun n => (upperCoefficient a r n : ℂ)) := by
    simpa only [one_pow, mul_one] using (upperCoefficient_hasSum a ha0 r hr 1 (by simpa using ha)).summable
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hs.norm

theorem upperBoundary_hasSum {T : ℝ} (a : ℝ) (ha0 : a ≠ 0) (ha : |a| < 1)
    (r : ℕ) (hr : 1 ≤ r) (t : AddCircle T) :
    HasSum (fun n => (upperCoefficient a r n : ℂ) * fourier (n : ℤ) t) (upperBoundary a r t) := by
  simpa only [upperBoundary, fourier_nat_eq_pow] using
    upperCoefficient_hasSum a ha0 r hr (fourier 1 t) (by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, fourier_apply, Circle.norm_coe, mul_one] using ha)

theorem upperBoundary_fourierCoeff_nat {T : ℝ} [Fact (0 < T)]
    (a : ℝ) (ha0 : a ≠ 0) (ha : |a| < 1) (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    fourierCoeff (upperBoundary (T := T) a r) (n : ℤ) = (upperCoefficient a r n : ℂ) := by
  have hs := hasSum_fourierCoeff_of_pointwise (T := T)
    (fun k => (upperCoefficient a r k : ℂ)) (fun k : ℕ => (k : ℤ)) (upperBoundary a r)
    (by simpa using upperCoefficient_summable_abs a ha0 ha r hr)
    (upperBoundary_hasSum a ha0 ha r hr) (n : ℤ)
  have he : (fun k : ℕ => (upperCoefficient a r k : ℂ) * (Pi.single (k : ℤ) (1 : ℂ) : ℤ → ℂ) (n : ℤ)) =
      (fun k => if k = n then (upperCoefficient a r n : ℂ) else 0) := by
    funext k
    by_cases h : k = n
    · subst k; simp
    · have hnk : (n : ℤ) ≠ (k : ℤ) := by exact_mod_cast Ne.symm h
      simp only [Pi.single_apply, ite_eq_right hnk, ite_eq_right h, mul_zero]
  rw [he] at hs
  exact hs.unique (hasSum_ite_eq n (upperCoefficient a r n : ℂ))

theorem fourier_two_pi_coe (n : ℤ) (t : ℝ) :
    @fourier (2 * Real.pi) n (t : AddCircle (2 * Real.pi)) =
      Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp

theorem upperBoundary_coe (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (r : ℕ) (t : ℝ) :
    upperBoundary a r (t : AddCircle (2 * Real.pi)) = boundaryAmplitude a t *
      Complex.exp (Complex.I * (((r - 1 : ℕ) : ℂ) * (realPhase a t : ℂ))) := by
  have hpoint : @fourier (2 * Real.pi) 1 (t : AddCircle (2 * Real.pi)) = circlePoint t := by
    rw [fourier_two_pi_coe]
    simp only [Int.cast_one, mul_one, circlePoint]
  unfold upperBoundary
  rw [hpoint, realPhase_lifts_blaschke a ha0.le ha1 t, ← Complex.exp_nat_mul]
  change boundaryAmplitude a t * _ = _
  congr 2
  ring

/-- The coefficient is the actual normalized oscillatory integral, including its frequency sign. -/
theorem upperCoefficient_eq_oscillatory_integral (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    (upperCoefficient a r n : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), boundaryAmplitude a t *
        Complex.exp (Complex.I * ((((r - 1 : ℕ) : ℝ) * realPhase a t - (n : ℝ) * t : ℝ) : ℂ)) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have ha : |a| < 1 := by rwa [abs_of_pos ha0]
  rw [← upperBoundary_fourierCoeff_nat (T := 2 * Real.pi) a ha0.ne' ha r hr n,
    fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ = _
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [fourier_two_pi_coe, upperBoundary_coe a ha0 ha1]
  simp only [smul_eq_mul]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem upperCoefficient_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (r : ℕ) (hr : 2 ≤ r) (n : ℕ) :
    |upperCoefficient a r n| ≤ upperOscillationConstant a / Real.sqrt ((r : ℝ) - 1) := by
  have h := upperCandidate_oscillatory_integral a ha0 ha1 ((r - 1 : ℕ) : ℝ) (n : ℝ) (by exact_mod_cast (show 1 ≤ r - 1 by omega))
  rw [← upperCoefficient_eq_oscillatory_integral a ha0 ha1 r (by omega) n] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] using h

end LocalCertification.Asymptotic
