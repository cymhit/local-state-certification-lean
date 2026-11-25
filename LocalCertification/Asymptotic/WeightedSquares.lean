import LocalCertification.Asymptotic.BlaschkeEuler
import LocalCertification.Asymptotic.PoissonBoundary

open scoped BigOperators Topology
open MeasureTheory AddCircle Complex

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- Parseval for an actual absolutely summable natural-frequency expansion. -/
theorem analyticBoundary_hasSum_sq {T : ℝ} [Fact (0 < T)]
    (c : ℕ → ℂ) (F : C(AddCircle T, ℂ)) (hc : Summable (fun n => ‖c n‖))
    (hF : ∀ t, HasSum (fun n => c n * fourier (n : ℤ) t) (F t)) :
    HasSum (fun n => ‖c n‖ ^ 2) (∫ t, ‖F t‖ ^ 2 ∂haarAddCircle) := by
  have hpos (n : ℕ) : fourierCoeff F (n : ℤ) = c n := by
    have hs := hasSum_fourierCoeff_of_pointwise c (fun k : ℕ => (k : ℤ)) F hc hF (n : ℤ)
    have he : (fun k : ℕ => c k * (Pi.single (k : ℤ) (1 : ℂ) : ℤ → ℂ) (n : ℤ)) =
        (fun k => if k = n then c n else 0) := by
      funext k
      by_cases h : k = n
      · subst k; simp
      · have hnk : (n : ℤ) ≠ (k : ℤ) := by exact_mod_cast Ne.symm h
        simp only [Pi.single_apply, ite_eq_right hnk, ite_eq_right h, mul_zero]
    rw [he] at hs
    exact hs.unique (hasSum_ite_eq n (c n))
  have hneg (n : ℕ) : fourierCoeff F (-((n : ℤ) + 1)) = 0 := by
    have hs := hasSum_fourierCoeff_of_pointwise c (fun k : ℕ => (k : ℤ)) F hc hF (-((n : ℤ) + 1))
    have he : (fun k : ℕ => c k * (Pi.single (k : ℤ) (1 : ℂ) : ℤ → ℂ) (-((n : ℤ) + 1))) =
        fun _ => 0 := by
      funext k
      have hn : -((n : ℤ) + 1) ≠ (k : ℤ) := by omega
      simp only [Pi.single_apply, ite_eq_right hn, mul_zero]
    rw [he] at hs
    exact hs.unique hasSum_zero
  simpa only [hpos, hneg, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
    (continuous_hasSum_sq_fourierCoeff F).nat_add_neg_add_one

/-- The actual Euler rational function, restricted continuously to the unit circle. -/
def blaschkeEulerBoundary {T : ℝ} (a : ℝ) (ha : |a| < 1) (s : ℕ) :
    C(AddCircle T, ℂ) where
  toFun t := blaschkeEuler a s (fourier 1 t)
  continuous_toFun := by
    change Continuous (fun t : AddCircle T =>
      (s : ℂ) * blaschke a (fourier 1 t) ^ (s - 1) *
        ((((a : ℂ) ^ 2 - 1) * fourier 1 t) / (1 - (a : ℂ) * fourier 1 t) ^ 2))
    apply Continuous.mul
    · exact continuous_const.mul (blaschkeBoundary a ha (s - 1)).continuous
    · apply Continuous.div
      · exact continuous_const.mul (fourier 1).continuous
      · exact (continuous_const.sub (continuous_const.mul (fourier 1).continuous)).pow 2
      · intro t
        apply pow_ne_zero
        exact blaschke_denominator_ne_zero a _ (by
          simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, fourier_apply,
            Circle.norm_coe, mul_one] using ha)

theorem blaschkeEulerBoundary_hasSum {T : ℝ} (a : ℝ) (ha : |a| < 1)
    (s : ℕ) (t : AddCircle T) :
    HasSum (fun n : ℕ => ((n : ℂ) * (blaschkeCoeff a s n : ℂ)) * fourier (n : ℤ) t)
      (blaschkeEulerBoundary a ha s t) := by
  change HasSum _ (blaschkeEuler a s (fourier 1 t))
  simpa only [fourier_nat_eq_pow] using
    blaschkeEuler_hasSum a s (fourier 1 t) (by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, fourier_apply,
        Circle.norm_coe, mul_one] using ha)

theorem blaschkeEulerBoundary_norm {T : ℝ} (a : ℝ) (ha : |a| < 1)
    (s : ℕ) (t : AddCircle T) :
    ‖blaschkeEulerBoundary a ha s t‖ = (s : ℝ) * ‖poissonBoundary a ha t‖ := by
  have hz : ‖fourier 1 t‖ = 1 := Circle.norm_coe _
  change ‖(s : ℂ) * blaschke a (fourier 1 t) ^ (s - 1) *
    blaschkeBaseEuler a (fourier 1 t)‖ = _
  rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow,
    blaschke_norm_of_norm_eq_one a ha (fourier 1 t) hz, one_pow, mul_one]
  congr 1
  rw [poissonBoundary_eq_real, Complex.norm_real, Real.norm_eq_abs]
  have hn : ‖(a : ℂ) ^ 2 - 1‖ = |a ^ 2 - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  simp only [blaschkeBaseEuler, norm_div, norm_mul, norm_pow, hz, mul_one,
    hn, abs_div, abs_pow, abs_norm]
  rw [abs_sub_comm]

/-- Exact weighted square sum of the constructed real coefficients, including `s = 0`. -/
theorem blaschkeCoeff_hasSum_weighted_sq (a : ℝ) (ha : |a| < 1) (s : ℕ) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * blaschkeCoeff a s n ^ 2)
      ((s : ℝ) ^ 2 * ((1 + a ^ 2) / (1 - a ^ 2))) := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hc : Summable (fun n : ℕ => ‖(n : ℂ) * (blaschkeCoeff a s n : ℂ)‖) := by
    simpa using blaschkeEuler_summable_norm a s 1 (by simpa using ha)
  have hs := analyticBoundary_hasSum_sq (fun n : ℕ => (n : ℂ) * (blaschkeCoeff a s n : ℂ))
    (blaschkeEulerBoundary (T := 1) a ha s) hc (blaschkeEulerBoundary_hasSum a ha s)
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs] at hs
  simp_rw [blaschkeEulerBoundary_norm, mul_pow] at hs
  rw [integral_const_mul, poissonBoundary_integral_norm_sq] at hs
  exact hs

end LocalCertification.Asymptotic
