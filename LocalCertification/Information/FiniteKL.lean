import LocalCertification.Information.FiniteAtoms

set_option autoImplicit false
open scoped ENNReal BigOperators
open MeasureTheory InformationTheory Set
noncomputable section
namespace LocalCertification.Information

/-- The elementary KL integrand bound includes a zero numerator. -/
theorem klFun_le_square {t : ℝ} (ht : 0 ≤ t) : klFun t ≤ (t-1)^2 := by
  rcases eq_or_lt_of_le ht with h | h
  · simp [← h, klFun]
  · have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) ht
    rw [klFun_apply]
    nlinarith

theorem weighted_klFun_le_square {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    q*klFun (p/q) ≤ (p-q)^2/q := by
  have h := mul_le_mul_of_nonneg_left (klFun_le_square (div_nonneg hp hq.le)) hq.le
  calc
    _ ≤ q*(p/q-1)^2 := h
    _ = _ := by field_simp

variable {O : Type*} [MeasurableSpace O] [Fintype O] [MeasurableSingletonClass O]

omit [Fintype O] [MeasurableSingletonClass O] in
/-- Positive denominator atoms imply actual measure absolute continuity. -/
theorem absolutelyContinuous_of_pos_atoms (P Q : Measure O) (hQ : ∀ o, Q {o} ≠ 0) : P ≪ Q := by
  intro s hs
  have he : s = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro o ho
    exact hQ o (measure_mono_null (Set.singleton_subset_iff.mpr ho) hs)
  simp [he]

/-- Finite actual Measure KL is bounded by the classical chi-square sum. -/
theorem finite_klDiv_le_chiSq (P Q : Measure O) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hQ : ∀ o, 0 < (Q {o}).toReal) :
    klDiv P Q ≤ ENNReal.ofReal (∑ o : O, ((P {o}).toReal-(Q {o}).toReal)^2/(Q {o}).toReal) := by
  have hAC := absolutelyContinuous_of_pos_atoms P Q (fun o h => by simpa [h] using hQ o)
  rw [finite_klDiv_eq_sum hAC]
  calc
    _ ≤ ∑ o : O, ENNReal.ofReal (((P {o}).toReal-(Q {o}).toReal)^2/(Q {o}).toReal) := by
      apply Finset.sum_le_sum
      intro o _
      rw [atomKL, ← ENNReal.ofReal_toReal (measure_ne_top Q {o}),
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal (weighted_klFun_le_square ENNReal.toReal_nonneg (hQ o))
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro o _
      positivity

/-- A uniform positive floor yields the squared Euclidean atom bound, with genuine ENNReal KL. -/
theorem finite_klDiv_le_floor (P Q : Measure O) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {δ : ℝ} (hδ : 0 < δ) (hQ : ∀ o, δ ≤ (Q {o}).toReal) :
    klDiv P Q ≤ ENNReal.ofReal (δ⁻¹*∑ o : O, ((P {o}).toReal-(Q {o}).toReal)^2) := by
  apply (finite_klDiv_le_chiSq P Q (fun o => hδ.trans_le (hQ o))).trans
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  simpa only [div_eq_mul_inv, mul_comm] using
    div_le_div_of_nonneg_left (sq_nonneg ((P {o}).toReal-(Q {o}).toReal)) hδ (hQ o)

end LocalCertification.Information
