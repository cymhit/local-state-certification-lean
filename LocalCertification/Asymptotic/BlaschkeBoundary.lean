import LocalCertification.Asymptotic.BlaschkeCoefficients
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open scoped BigOperators Topology
open MeasureTheory AddCircle Complex

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- On the unit circle the actual Blaschke factor has modulus one. -/
theorem blaschke_norm_of_norm_eq_one (a : ℝ) (ha : |a| < 1)
    (z : ℂ) (hz : ‖z‖ = 1) : ‖blaschke a z‖ = 1 := by
  have hden : 1 - (a : ℂ) * z ≠ 0 :=
    blaschke_denominator_ne_zero a z (by simpa [norm_mul, hz] using ha)
  have hsq : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  have he : Complex.normSq ((a : ℂ) - z) = Complex.normSq (1 - (a : ℂ) * z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im] at hsq ⊢
    have hs := congrArg (fun x : ℝ => a ^ 2 * x) hsq
    nlinarith [hs]
  have hn : ‖(a : ℂ) - z‖ = ‖1 - (a : ℂ) * z‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg ((a : ℂ) - z), norm_nonneg (1 - (a : ℂ) * z)]
  rw [blaschke, norm_div, hn, div_self (norm_ne_zero_iff.mpr hden)]

/-- Fourier coefficients may be read from any absolutely summable actual character series. -/
theorem hasSum_fourierCoeff_of_pointwise {T : ℝ} [Fact (0 < T)]
    {ι : Type*} [Countable ι] (c : ι → ℂ) (frequency : ι → ℤ)
    (F : AddCircle T → ℂ) (hc : Summable (fun i => ‖c i‖))
    (hF : ∀ t, HasSum (fun i => c i * fourier (frequency i) t) (F t)) (m : ℤ) :
    HasSum (fun i => c i * (Pi.single (frequency i) (1 : ℂ) : ℤ → ℂ) m) (fourierCoeff F m) := by
  have hi := hasSum_integral_of_dominated_convergence
    (μ := (haarAddCircle : Measure (AddCircle T)))
    (F := fun i t => fourier (-m) t * (c i * fourier (frequency i) t))
    (f := fun t => fourier (-m) t * F t)
    (fun i _ => ‖c i‖)
    (fun i => ((fourier (-m)).continuous.mul
      (continuous_const.mul (fourier (frequency i)).continuous)).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall (fun t => by
      simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul, mul_one, le_refl]))
    (Filter.Eventually.of_forall (fun _ => hc))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun t => (hF t).mul_left (fourier (-m) t)))
  convert hi using 1
  · funext i
    change c i * (Pi.single (frequency i) (1 : ℂ) : ℤ → ℂ) m =
      fourierCoeff (fun t => c i * fourier (frequency i) t) m
    rw [fourierCoeff.const_mul, fourierCoeff_fourier]
  · rfl

/-- Natural powers of the first circle character are exactly its natural frequencies. -/
theorem fourier_nat_eq_pow {T : ℝ} (n : ℕ) (t : AddCircle T) :
    fourier (n : ℤ) t = (fourier 1 t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

/-- The continuous boundary function is the specified rational function power. -/
def blaschkeBoundary {T : ℝ} (a : ℝ) (ha : |a| < 1) (s : ℕ) :
    C(AddCircle T, ℂ) where
  toFun t := blaschke a (fourier 1 t) ^ s
  continuous_toFun := by
    apply Continuous.pow
    apply Continuous.div
    · exact continuous_const.sub (fourier 1).continuous
    · exact continuous_const.sub (continuous_const.mul (fourier 1).continuous)
    · intro t
      exact blaschke_denominator_ne_zero a _ (by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, fourier_apply,
          Circle.norm_coe, mul_one] using ha)

theorem blaschkeBoundary_hasSum {T : ℝ} (a : ℝ) (ha : |a| < 1) (s : ℕ)
    (t : AddCircle T) :
    HasSum (fun n => (blaschkeCoeff a s n : ℂ) * fourier (n : ℤ) t)
      (blaschkeBoundary a ha s t) := by
  change HasSum _ (blaschke a (fourier 1 t) ^ s)
  simpa only [fourier_nat_eq_pow] using
    blaschkeCoeff_hasSum a s (fourier 1 t) (by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, fourier_apply,
        Circle.norm_coe, mul_one] using ha)

theorem blaschkeBoundary_fourierCoeff_nat {T : ℝ} [Fact (0 < T)]
    (a : ℝ) (ha : |a| < 1) (s n : ℕ) :
    fourierCoeff (blaschkeBoundary (T := T) a ha s) (n : ℤ) = blaschkeCoeff a s n := by
  have hs := hasSum_fourierCoeff_of_pointwise (T := T)
    (fun k => (blaschkeCoeff a s k : ℂ)) (fun k : ℕ => (k : ℤ))
    (blaschkeBoundary a ha s) (by simpa using blaschkeCoeff_summable_abs a ha s)
    (blaschkeBoundary_hasSum a ha s) (n : ℤ)
  have he : (fun k : ℕ => (blaschkeCoeff a s k : ℂ) * (Pi.single (k : ℤ) (1 : ℂ) : ℤ → ℂ) (n : ℤ)) =
      (fun k => if k = n then (blaschkeCoeff a s n : ℂ) else 0) := by
    funext k
    by_cases h : k = n
    · subst k
      simp
    · have hnk : (n : ℤ) ≠ (k : ℤ) := by exact_mod_cast Ne.symm h
      simp only [Pi.single_apply, ite_eq_right hnk, ite_eq_right h, mul_zero]
  rw [he] at hs
  exact hs.unique (hasSum_ite_eq n (blaschkeCoeff a s n : ℂ))

theorem blaschkeBoundary_fourierCoeff_neg {T : ℝ} [Fact (0 < T)]
    (a : ℝ) (ha : |a| < 1) (s n : ℕ) :
    fourierCoeff (blaschkeBoundary (T := T) a ha s) (-(n + 1 : ℕ) : ℤ) = 0 := by
  have hs := hasSum_fourierCoeff_of_pointwise (T := T)
    (fun k => (blaschkeCoeff a s k : ℂ)) (fun k : ℕ => (k : ℤ))
    (blaschkeBoundary a ha s) (by simpa using blaschkeCoeff_summable_abs a ha s)
    (blaschkeBoundary_hasSum a ha s) (-(n + 1 : ℕ) : ℤ)
  have he : (fun k : ℕ => (blaschkeCoeff a s k : ℂ) *
      (Pi.single (k : ℤ) (1 : ℂ) : ℤ → ℂ) (-(n + 1 : ℕ) : ℤ)) = fun _ => 0 := by
    funext k
    have hn : (-(n + 1 : ℕ) : ℤ) ≠ (k : ℤ) := by omega
    simp only [Pi.single_apply, ite_eq_right hn, mul_zero]
  rw [he] at hs
  exact hs.unique hasSum_zero

theorem blaschkeBoundary_norm {T : ℝ} (a : ℝ) (ha : |a| < 1)
    (s : ℕ) (t : AddCircle T) : ‖blaschkeBoundary a ha s t‖ = 1 := by
  change ‖blaschke a (fourier 1 t) ^ s‖ = 1
  rw [norm_pow, blaschke_norm_of_norm_eq_one a ha (fourier 1 t) (Circle.norm_coe _), one_pow]

/-- Parseval for an actual continuous circle function, with normalized Haar measure. -/
theorem continuous_hasSum_sq_fourierCoeff {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) :
    HasSum (fun k : ℤ => ‖fourierCoeff F k‖ ^ 2)
      (∫ t, ‖F t‖ ^ 2 ∂(haarAddCircle : Measure (AddCircle T))) := by
  have hs := hasSum_sq_fourierCoeff (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ F)
  simp_rw [fourierCoeff_toLp] at hs
  convert hs using 1
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle F] with t ht
  rw [ht]

/-- The first exact square-sum identity for the constructed real Blaschke coefficients. -/
theorem blaschkeCoeff_hasSum_sq (a : ℝ) (ha : |a| < 1) (s : ℕ) :
    HasSum (fun n => blaschkeCoeff a s n ^ 2) 1 := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hs := continuous_hasSum_sq_fourierCoeff (blaschkeBoundary (T := 1) a ha s)
  simp_rw [blaschkeBoundary_norm] at hs
  have hs' := hs.nat_add_neg_add_one
  have hn (n : ℕ) : fourierCoeff (blaschkeBoundary (T := 1) a ha s) (-((n : ℤ) + 1)) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      blaschkeBoundary_fourierCoeff_neg (T := 1) a ha s n
  simp only [blaschkeBoundary_fourierCoeff_nat, hn, norm_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, one_pow] at hs'
  simpa using hs'

end LocalCertification.Asymptotic
