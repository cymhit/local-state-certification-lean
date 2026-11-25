import LocalCertification.Asymptotic.BlaschkeBoundary

open scoped BigOperators Topology ComplexConjugate
open MeasureTheory AddCircle Complex

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The actual Poisson kernel on the circle, written without an argument branch. -/
def poissonBoundary {T : ℝ} (a : ℝ) (ha : |a| < 1) : C(AddCircle T, ℂ) where
  toFun t := (1 - (a : ℂ) ^ 2) /
    ((1 - (a : ℂ) * fourier 1 t) * (1 - (a : ℂ) * conj (fourier 1 t)))
  continuous_toFun := by
    apply Continuous.div continuous_const
    · exact (continuous_const.sub (continuous_const.mul (fourier 1).continuous)).mul
        (continuous_const.sub (continuous_const.mul
          (Complex.continuous_conj.comp (fourier 1).continuous)))
    · intro t
      apply mul_ne_zero
      · exact blaschke_denominator_ne_zero a _ (by
          simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, fourier_apply,
            Circle.norm_coe, mul_one] using ha)
      · exact blaschke_denominator_ne_zero a _ (by
          simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_conj, fourier_apply,
            Circle.norm_coe, mul_one] using ha)

/-- The displayed complex rational expression is the usual real Poisson kernel. -/
theorem poissonBoundary_eq_real {T : ℝ} (a : ℝ) (ha : |a| < 1) (t : AddCircle T) :
    poissonBoundary a ha t = ((1 - a ^ 2) / ‖1 - (a : ℂ) * fourier 1 t‖ ^ 2 : ℝ) := by
  change (1 - (a : ℂ) ^ 2) / _ = _
  have hc : 1 - (a : ℂ) * conj (fourier 1 t) = conj (1 - (a : ℂ) * fourier 1 t) := by simp
  rw [hc, Complex.mul_conj']
  push_cast
  rfl

private theorem poisson_geometric_split {T : ℝ} (a : ℝ) (ha : |a| < 1)
    (t : AddCircle T) :
    (1 - (a : ℂ) * fourier 1 t)⁻¹ +
      ((a : ℂ) * conj (fourier 1 t)) / (1 - (a : ℂ) * conj (fourier 1 t)) =
      poissonBoundary a ha t := by
  have hz : ‖fourier 1 t‖ = 1 := Circle.norm_coe _
  have h₁ : 1 - (a : ℂ) * fourier 1 t ≠ 0 :=
    blaschke_denominator_ne_zero a _ (by simpa [norm_mul, hz] using ha)
  have h₂ : 1 - (a : ℂ) * conj (fourier 1 t) ≠ 0 :=
    blaschke_denominator_ne_zero a _ (by simpa [norm_mul, hz] using ha)
  have hu : fourier 1 t * conj (fourier 1 t) = 1 := by rw [Complex.mul_conj', hz]; simp
  change _ = (1 - (a : ℂ) ^ 2) / _
  field_simp
  linear_combination -(a : ℂ) ^ 2 * hu

theorem poissonBoundary_hasSum {T : ℝ} (a : ℝ) (ha : |a| < 1) (t : AddCircle T) :
    HasSum (fun k : ℤ => (a : ℂ) ^ k.natAbs * fourier k t) (poissonBoundary a ha t) := by
  have hz : ‖fourier 1 t‖ = 1 := Circle.norm_coe _
  have hp : ‖(a : ℂ) * fourier 1 t‖ < 1 := by simpa [norm_mul, hz] using ha
  have hm : ‖(a : ℂ) * conj (fourier 1 t)‖ < 1 := by simpa [norm_mul, hz] using ha
  have hs₁ : HasSum (fun n : ℕ => (a : ℂ) ^ (n : ℤ).natAbs * fourier (n : ℤ) t)
      (1 - (a : ℂ) * fourier 1 t)⁻¹ := by
    simpa only [Int.natAbs_natCast, fourier_nat_eq_pow, mul_pow] using
      hasSum_geometric_of_norm_lt_one hp
  have hs₂ : HasSum
      (fun n : ℕ => (a : ℂ) ^ (-(n : ℤ) - 1).natAbs * fourier (-(n : ℤ) - 1) t)
      (((a : ℂ) * conj (fourier 1 t)) / (1 - (a : ℂ) * conj (fourier 1 t))) := by
    have he (n : ℕ) : (-(n : ℤ) - 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    simp_rw [he, Int.natAbs_neg, Int.natAbs_natCast, fourier_neg, fourier_nat_eq_pow, map_pow]
    have hs := (hasSum_geometric_of_norm_lt_one hm).mul_left ((a : ℂ) * conj (fourier 1 t))
    convert hs using 1
    · funext n
      simp only [mul_pow, pow_succ']
      ring
    · rfl
  have hs₂' : HasSum
      (fun n : ℕ => (a : ℂ) ^ (-((n : ℤ) + 1)).natAbs * fourier (-((n : ℤ) + 1)) t)
      (((a : ℂ) * conj (fourier 1 t)) / (1 - (a : ℂ) * conj (fourier 1 t))) := by
    simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using hs₂
  rw [← poisson_geometric_split a ha t]
  exact HasSum.of_nat_of_neg_add_one
    (f := fun k : ℤ => (a : ℂ) ^ k.natAbs * fourier k t) hs₁ hs₂'

theorem poissonCoeff_summable_norm (a : ℝ) (ha : |a| < 1) :
    Summable (fun k : ℤ => ‖(a : ℂ) ^ k.natAbs‖) := by
  have hs := hasSum_geometric_of_lt_one (abs_nonneg a) ha
  have hp : HasSum (fun n : ℕ => |a| ^ (n : ℤ).natAbs) (1 - |a|)⁻¹ := by simpa using hs
  have hn : HasSum (fun n : ℕ => |a| ^ (-((n : ℤ) + 1)).natAbs)
      (|a| * (1 - |a|)⁻¹) := by
    have he (n : ℕ) : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    simp_rw [he, Int.natAbs_neg, Int.natAbs_natCast, pow_succ']
    exact hs.mul_left |a|
  simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs] using
    (HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => |a| ^ k.natAbs) hp hn).summable

theorem poissonBoundary_fourierCoeff {T : ℝ} [Fact (0 < T)]
    (a : ℝ) (ha : |a| < 1) (k : ℤ) :
    fourierCoeff (poissonBoundary (T := T) a ha) k = (a : ℂ) ^ k.natAbs := by
  have hs := hasSum_fourierCoeff_of_pointwise (T := T) (fun k : ℤ => (a : ℂ) ^ k.natAbs)
    id (poissonBoundary a ha) (poissonCoeff_summable_norm a ha)
    (poissonBoundary_hasSum a ha) k
  have he : (fun i : ℤ => (a : ℂ) ^ i.natAbs * (Pi.single i (1 : ℂ) : ℤ → ℂ) k) =
      (fun i => if i = k then (a : ℂ) ^ k.natAbs else 0) := by
    funext i
    by_cases h : i = k
    · subst i; simp
    · simp only [Pi.single_apply, ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]
  change HasSum (fun i : ℤ => (a : ℂ) ^ i.natAbs * (Pi.single i (1 : ℂ) : ℤ → ℂ) k) _ at hs
  rw [he] at hs
  exact hs.unique (hasSum_ite_eq k ((a : ℂ) ^ k.natAbs))

private theorem norm_real_pow_sq (a : ℝ) (n : ℕ) :
    ‖(a : ℂ) ^ n‖ ^ 2 = (a ^ 2) ^ n := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_right_comm, sq_abs]

theorem poissonCoeff_hasSum_sq (a : ℝ) (ha : |a| < 1) :
    HasSum (fun k : ℤ => ‖(a : ℂ) ^ k.natAbs‖ ^ 2) ((1 + a ^ 2) / (1 - a ^ 2)) := by
  have ha2 : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).mpr ha
  have hs := hasSum_geometric_of_lt_one (sq_nonneg a) ha2
  have hp : HasSum (fun n : ℕ => ‖(a : ℂ) ^ (n : ℤ).natAbs‖ ^ 2)
      (1 - a ^ 2)⁻¹ := by simpa only [Int.natAbs_natCast, norm_real_pow_sq] using hs
  have hn : HasSum (fun n : ℕ => ‖(a : ℂ) ^ (-((n : ℤ) + 1)).natAbs‖ ^ 2)
      (a ^ 2 * (1 - a ^ 2)⁻¹) := by
    have he (n : ℕ) : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    simp_rw [he, Int.natAbs_neg, Int.natAbs_natCast, norm_real_pow_sq]
    convert hs.mul_left (a ^ 2) using 1
    funext n
    exact pow_succ' (a ^ 2) n
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun k : ℤ => ‖(a : ℂ) ^ k.natAbs‖ ^ 2) hp hn
  convert h using 1
  field_simp

theorem poissonBoundary_integral_norm_sq {T : ℝ} [Fact (0 < T)]
    (a : ℝ) (ha : |a| < 1) :
    (∫ t, ‖poissonBoundary a ha t‖ ^ 2 ∂(haarAddCircle : Measure (AddCircle T))) =
      (1 + a ^ 2) / (1 - a ^ 2) := by
  have hs := continuous_hasSum_sq_fourierCoeff (poissonBoundary (T := T) a ha)
  simp_rw [poissonBoundary_fourierCoeff] at hs
  exact hs.unique (poissonCoeff_hasSum_sq a ha)

end LocalCertification.Asymptotic
