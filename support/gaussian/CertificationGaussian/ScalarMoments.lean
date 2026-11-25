import CertificationGaussian.WickOrthogonality
import Mathlib.Probability.Independence.Integration

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CertificationGaussian

/-- All ordinary powers are integrable for the actual standard real Gaussian. -/
@[fun_prop] theorem standardGaussian_integrable_pow (n : Nat) :
    Integrable (fun x : ℝ => x^n) (gaussianReal 0 1) := by
  exact integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : ℝ => x) (by simp [integrableExpSet_fun_id_gaussianReal]) n

/-- Hermite expectations follow from the already proved Wick orthogonality. -/
theorem standardGaussian_wick_mean {n : Nat} (hn : n ≠ 0) :
    ∫ x : ℝ, wickMonomial n 1 x ∂gaussianReal 0 1 = 0 := by
  simpa [hn] using GaussianField.wickMonomial_inner_gaussianReal_one n 0

theorem standardGaussian_moment_two :
    ∫ x : ℝ, x^2 ∂gaussianReal 0 1 = 1 := by
  have h := standardGaussian_wick_mean (n := 2) (by decide)
  have he (x : ℝ) : wickMonomial 2 1 x = x^2 - 1 := by simp [wickMonomial]; ring
  simp_rw [he] at h
  erw [integral_sub (standardGaussian_integrable_pow 2) (integrable_const 1)] at h
  norm_num at h
  linarith

theorem standardGaussian_moment_four :
    ∫ x : ℝ, x^4 ∂gaussianReal 0 1 = 3 := by
  have h := standardGaussian_wick_mean (n := 4) (by decide)
  have he (x : ℝ) : wickMonomial 4 1 x = x^4 - 6*x^2 + 3 := by
    norm_num [wickMonomial]; ring
  simp_rw [he] at h
  erw [integral_add ((standardGaussian_integrable_pow 4).sub
    ((standardGaussian_integrable_pow 2).const_mul 6)) (integrable_const 3),
    integral_sub (standardGaussian_integrable_pow 4)
      ((standardGaussian_integrable_pow 2).const_mul 6), integral_const_mul,
    standardGaussian_moment_two] at h
  norm_num at h ⊢
  linarith

theorem standardGaussian_moment_six :
    ∫ x : ℝ, x^6 ∂gaussianReal 0 1 = 15 := by
  have h := standardGaussian_wick_mean (n := 6) (by decide)
  have he (x : ℝ) : wickMonomial 6 1 x = x^6 - 15*x^4 + 45*x^2 - 15 := by
    norm_num [wickMonomial]; ring
  simp_rw [he] at h
  erw [integral_sub (((standardGaussian_integrable_pow 6).sub
      ((standardGaussian_integrable_pow 4).const_mul 15)).add
      ((standardGaussian_integrable_pow 2).const_mul 45)) (integrable_const 15),
    integral_add ((standardGaussian_integrable_pow 6).sub
      ((standardGaussian_integrable_pow 4).const_mul 15))
      ((standardGaussian_integrable_pow 2).const_mul 45),
    integral_sub (standardGaussian_integrable_pow 6)
      ((standardGaussian_integrable_pow 4).const_mul 15), integral_const_mul,
    integral_const_mul, standardGaussian_moment_four, standardGaussian_moment_two] at h
  norm_num at h ⊢
  linarith

theorem standardGaussian_moment_eight :
    ∫ x : ℝ, x^8 ∂gaussianReal 0 1 = 105 := by
  have h := standardGaussian_wick_mean (n := 8) (by decide)
  have he (x : ℝ) : wickMonomial 8 1 x = x^8 - 28*x^6 + 210*x^4 - 420*x^2 + 105 := by
    norm_num [wickMonomial]; ring
  simp_rw [he] at h
  erw [integral_add ((((standardGaussian_integrable_pow 8).sub
      ((standardGaussian_integrable_pow 6).const_mul 28)).add
      ((standardGaussian_integrable_pow 4).const_mul 210)).sub
      ((standardGaussian_integrable_pow 2).const_mul 420)) (integrable_const 105),
    integral_sub (((standardGaussian_integrable_pow 8).sub
      ((standardGaussian_integrable_pow 6).const_mul 28)).add
      ((standardGaussian_integrable_pow 4).const_mul 210))
      ((standardGaussian_integrable_pow 2).const_mul 420),
    integral_add ((standardGaussian_integrable_pow 8).sub
      ((standardGaussian_integrable_pow 6).const_mul 28))
      ((standardGaussian_integrable_pow 4).const_mul 210),
    integral_sub (standardGaussian_integrable_pow 8)
      ((standardGaussian_integrable_pow 6).const_mul 28), integral_const_mul,
    integral_const_mul, integral_const_mul,
    standardGaussian_moment_six, standardGaussian_moment_four, standardGaussian_moment_two] at h
  norm_num at h ⊢
  linarith

/-- The exact centered squared modulus of two normalized real Gaussian coordinates. -/
def radialPairOutcome (z : ℝ × ℝ) : ℝ := (z.1^2 + z.2^2) / 2 - 1

abbrev standardGaussianPair : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

@[fun_prop] theorem standardPair_integrable_monomial (a b : Nat) :
    Integrable (fun z : ℝ × ℝ => z.1^a * z.2^b) standardGaussianPair :=
  (standardGaussian_integrable_pow a).mul_prod (standardGaussian_integrable_pow b)

@[fun_prop] theorem standardPair_integrable_fst_pow (a : Nat) :
    Integrable (fun z : ℝ × ℝ => z.1^a) standardGaussianPair := by
  simpa using standardPair_integrable_monomial a 0

@[fun_prop] theorem standardPair_integrable_snd_pow (a : Nat) :
    Integrable (fun z : ℝ × ℝ => z.2^a) standardGaussianPair := by
  simpa using standardPair_integrable_monomial 0 a

theorem standardPair_integral_monomial (a b : Nat) :
    ∫ z : ℝ × ℝ, z.1^a * z.2^b ∂standardGaussianPair =
      (∫ x : ℝ, x^a ∂gaussianReal 0 1) * (∫ x : ℝ, x^b ∂gaussianReal 0 1) :=
  integral_prod_mul _ _

theorem standardPair_integral_fst_pow (a : Nat) :
    ∫ z : ℝ × ℝ, z.1^a ∂standardGaussianPair = ∫ x : ℝ, x^a ∂gaussianReal 0 1 := by
  simpa using standardPair_integral_monomial a 0

theorem standardPair_integral_snd_pow (a : Nat) :
    ∫ z : ℝ × ℝ, z.2^a ∂standardGaussianPair = ∫ x : ℝ, x^a ∂gaussianReal 0 1 := by
  simpa using standardPair_integral_monomial 0 a

@[fun_prop] theorem radialPairOutcome_continuous : Continuous radialPairOutcome := by
  unfold radialPairOutcome; fun_prop

theorem radialPairOutcome_mean : ∫ z, radialPairOutcome z ∂standardGaussianPair = 0 := by
  unfold radialPairOutcome
  conv_lhs => arg 2; ext z; ring_nf
  simp (disch := fun_prop) only [integral_add, integral_mul_const,
    standardPair_integral_fst_pow, standardPair_integral_snd_pow,
    standardGaussian_moment_two, integral_const]
  norm_num

theorem radialPairOutcome_moment_two :
    ∫ z, (radialPairOutcome z)^2 ∂standardGaussianPair = 1 := by
  unfold radialPairOutcome
  conv_lhs => arg 2; ext z; ring_nf
  simp (disch := fun_prop) only [integral_add, integral_sub, integral_mul_const,
    standardPair_integral_monomial, standardPair_integral_fst_pow,
    standardPair_integral_snd_pow, standardGaussian_moment_two,
    standardGaussian_moment_four, integral_const]
  norm_num

theorem radialPairOutcome_moment_three :
    ∫ z, (radialPairOutcome z)^3 ∂standardGaussianPair = 2 := by
  unfold radialPairOutcome
  conv_lhs => arg 2; ext z; ring_nf
  simp (disch := fun_prop) only [integral_add, integral_mul_const,
    standardPair_integral_monomial, standardPair_integral_fst_pow,
    standardPair_integral_snd_pow, standardGaussian_moment_two,
    standardGaussian_moment_four, standardGaussian_moment_six, integral_const]
  norm_num

theorem radialPairOutcome_moment_four :
    ∫ z, (radialPairOutcome z)^4 ∂standardGaussianPair = 9 := by
  unfold radialPairOutcome
  conv_lhs => arg 2; ext z; ring_nf
  simp (disch := fun_prop) only [integral_add, integral_sub, integral_mul_const,
    standardPair_integral_monomial, standardPair_integral_fst_pow,
    standardPair_integral_snd_pow, standardGaussian_moment_two,
    standardGaussian_moment_four, standardGaussian_moment_six,
    standardGaussian_moment_eight, integral_const]
  norm_num

/-- The powers needed for the quartic variance expansion are actually integrable. -/
theorem radialPairOutcome_integrable_pow (n : Nat) (hn : n ≤ 4) :
    Integrable (fun z => (radialPairOutcome z)^n) standardGaussianPair := by
  interval_cases n <;>
    (conv => arg 1; ext z; unfold radialPairOutcome; ring_nf) <;> fun_prop

end CertificationGaussian
