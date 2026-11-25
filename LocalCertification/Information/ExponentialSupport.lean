import LocalCertification.Information.SingularFiniteKL

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Information

/-- Exponential affine supports of the nonnegative KL integrand, including a zero source. -/
theorem exponential_support_le_klFun (u t : ℝ) (hu : 0 ≤ u) :
    t * u - (Real.exp t - 1) ≤ klFun u := by
  rcases eq_or_lt_of_le hu with h | h
  · subst u
    simp only [mul_zero, klFun_zero]
    linarith [Real.exp_pos t]
  · have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t - Real.log u)) hu
    rw [Real.exp_sub, Real.exp_log h, div_mul_cancel₀ _ h.ne'] at he
    rw [klFun_apply]
    nlinarith

/-- A single full perspective dominates every affine support; positive-over-zero remains infinite. -/
theorem exponential_support_le_atomPerspective {O : Type*} [MeasurableSpace O]
    (P Q : Measure O) [IsFiniteMeasure P] [IsFiniteMeasure Q] (o : O) (t : ℝ) :
    ENNReal.ofReal (t * (P {o}).toReal - (Real.exp t - 1) * (Q {o}).toReal) ≤
      atomPerspective P Q o := by
  classical
  by_cases hQ : Q {o} = 0
  · by_cases hP : P {o} = 0
    · simp [atomPerspective, hQ, hP]
    · simp [atomPerspective, hQ, hP]
  · have hb : 0 < (Q {o}).toReal := ENNReal.toReal_pos hQ (measure_ne_top Q {o})
    have hs := mul_le_mul_of_nonneg_left
      (exponential_support_le_klFun ((P {o}).toReal / (Q {o}).toReal) t
        (div_nonneg ENNReal.toReal_nonneg hb.le)) hb.le
    have hid : (Q {o}).toReal *
        (t * ((P {o}).toReal / (Q {o}).toReal) - (Real.exp t - 1)) =
        t * (P {o}).toReal - (Real.exp t - 1) * (Q {o}).toReal := by
      field_simp
    rw [hid] at hs
    calc
      _ ≤ ENNReal.ofReal ((Q {o}).toReal *
          klFun ((P {o}).toReal / (Q {o}).toReal)) := ENNReal.ofReal_le_ofReal hs
      _ = atomPerspective P Q o := by
        rw [atomPerspective, ite_eq_right_iff.mpr (fun h => (hQ h).elim),
          atomKL, ENNReal.ofReal_mul hb.le, ENNReal.ofReal_toReal (measure_ne_top Q {o})]

/-- Taking positive parts is subadditive; the affine supports need not be nonnegative individually. -/
theorem ofReal_sum_le_sum_ofReal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-- Finite-measure variational lower support with no AC or finite-KL premise. -/
theorem finite_klDiv_exponential_support {O : Type*} [MeasurableSpace O]
    [Fintype O] [MeasurableSingletonClass O] (P Q : Measure O)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (t : O → ℝ) :
    ENNReal.ofReal (∑ o, (t o * (P {o}).toReal -
      (Real.exp (t o) - 1) * (Q {o}).toReal)) ≤ klDiv P Q := by
  rw [finite_klDiv_eq_sum_perspective]
  exact (ofReal_sum_le_sum_ofReal Finset.univ _).trans
    (Finset.sum_le_sum fun o _ => exponential_support_le_atomPerspective P Q o (t o))

end LocalCertification.Information
