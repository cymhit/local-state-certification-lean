import LocalCertification.Information.FinitePrefixProductDensity

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Information

theorem neg_mul_log_le_exp_neg_one {x : ℝ} (hx : 0 ≤ x) :
    -(x * Real.log x) ≤ Real.exp (-1) := by
  rcases eq_or_lt_of_le hx with hx | hx
  · simp [← hx, Real.exp_nonneg]
  have he := Real.exp_pos (-1 : ℝ)
  have h := Real.log_le_sub_one_of_pos (div_pos he hx)
  rw [Real.log_div (ne_of_gt he) (ne_of_gt hx), Real.log_exp] at h
  have hh := mul_le_mul_of_nonneg_left h (le_of_lt hx)
  have hc : x * (Real.exp (-1) / x) = Real.exp (-1) := by field_simp
  nlinarith

def relativeEntropyAtom (p q : ℝ) : ℝ := p * Real.log (p / q)
def negativeRelativeEntropyAtom (p q : ℝ) : ℝ := max (-relativeEntropyAtom p q) 0
def positiveRelativeEntropyAtom (p q : ℝ) : ℝ := max (relativeEntropyAtom p q) 0

theorem negativeRelativeEntropyAtom_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hzero : q = 0 → p = 0) :
    negativeRelativeEntropyAtom p q ≤ q * Real.exp (-1) := by
  by_cases hq0 : q = 0
  · simp [negativeRelativeEntropyAtom, relativeEntropyAtom, hq0, hzero hq0]
  have h := mul_le_mul_of_nonneg_left
    (neg_mul_log_le_exp_neg_one (div_nonneg hp hq)) hq
  have hc : q * (p / q) = p := by field_simp
  apply max_le
  · dsimp [relativeEntropyAtom]
    simpa only [mul_neg, ← mul_assoc, hc] using h
  · exact mul_nonneg hq (Real.exp_nonneg _)

theorem sum_negativeRelativeEntropyAtom_le {O : Type*} [Fintype O]
    (p q : O → ℝ) (hp : ∀ o, 0 ≤ p o) (hq : ∀ o, 0 ≤ q o)
    (hqsum : ∑ o, q o = 1) (hzero : ∀ o, q o = 0 → p o = 0) :
    ∑ o, negativeRelativeEntropyAtom (p o) (q o) ≤ Real.exp (-1) := by
  calc
    _ ≤ ∑ o, q o * Real.exp (-1) :=
      Finset.sum_le_sum (fun o _ => negativeRelativeEntropyAtom_le (hp o) (hq o) (hzero o))
    _ = Real.exp (-1) := by rw [← Finset.sum_mul, hqsum, one_mul]

theorem sum_positiveRelativeEntropyAtom_le {O : Type*} [Fintype O]
    (p q : O → ℝ) (hp : ∀ o, 0 ≤ p o) (hq : ∀ o, 0 ≤ q o)
    (hqsum : ∑ o, q o = 1) (hzero : ∀ o, q o = 0 → p o = 0)
    (L : ℝ) (hL : ∑ o, relativeEntropyAtom (p o) (q o) ≤ L) :
    ∑ o, positiveRelativeEntropyAtom (p o) (q o) ≤ L + Real.exp (-1) := by
  have hn := sum_negativeRelativeEntropyAtom_le p q hp hq hqsum hzero
  have he : (∑ o, positiveRelativeEntropyAtom (p o) (q o)) =
      (∑ o, relativeEntropyAtom (p o) (q o)) + ∑ o, negativeRelativeEntropyAtom (p o) (q o) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    dsimp [positiveRelativeEntropyAtom, negativeRelativeEntropyAtom]
    rcases le_total (relativeEntropyAtom (p o) (q o)) 0 with hh | hh
    · rw [max_eq_right hh, max_eq_left (neg_nonneg.mpr hh)]
      ring
    · rw [max_eq_left hh, max_eq_right (neg_nonpos.mpr hh)]
      ring
  linarith

variable {O : Type*} [MeasurableSpace O] [Fintype O] [MeasurableSingletonClass O]

theorem sum_real_finite_atoms (P : Measure O) [IsProbabilityMeasure P] :
    ∑ o, (P {o}).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun o _ => measure_ne_top P {o})]
  simp

theorem sum_relativeEntropyAtom_eq_klDiv (P Q : Measure O)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hAC : P ≪ Q) :
    ∑ o, relativeEntropyAtom (P {o}).toReal (Q {o}).toReal = (klDiv P Q).toReal := by
  rw [finite_klDiv_eq_sum hAC, ENNReal.toReal_sum]
  · have he (o : O) : (atomKL P Q o).toReal =
        relativeEntropyAtom (P {o}).toReal (Q {o}).toReal + (Q {o}).toReal - (P {o}).toReal := by
      rw [atomKL, ENNReal.toReal_mul, ENNReal.toReal_ofReal (atom_klFun_nonneg P Q o)]
      by_cases hq : Q {o} = 0
      · simp [hq, hAC hq, relativeEntropyAtom]
      have hqr : (Q {o}).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hq, measure_ne_top _ _⟩
      have hc : (Q {o}).toReal * ((P {o}).toReal / (Q {o}).toReal) = (P {o}).toReal := by field_simp
      dsimp [klFun, relativeEntropyAtom]
      rw [mul_sub, mul_add, ← mul_assoc, hc, mul_one]
    simp_rw [he]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_real_finite_atoms P,
      sum_real_finite_atoms Q]
    ring
  · intro o _
    unfold atomKL
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top


theorem integrable_finite_logLikelihood (P : Measure O) [IsFiniteMeasure P] (f : O → ℝ) :
    Integrable f P := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable (∑ o, ‖f o‖)
  exact Filter.Eventually.of_forall fun o =>
    Finset.single_le_sum (fun i _ => norm_nonneg (f i)) (Finset.mem_univ o)

theorem sum_abs_relativeEntropyAtom_le (P Q : Measure O) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (L : ℝ≥0∞) (hfinite : L ≠ ∞) (hL : klDiv P Q ≤ L) :
    ∑ o, |relativeEntropyAtom (P {o}).toReal (Q {o}).toReal| ≤
      L.toReal + 2 * Real.exp (-1) := by
  have hAC := (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top hfinite hL)).1
  have hz : ∀ o, (Q {o}).toReal = 0 → (P {o}).toReal = 0 := by
    intro o ho
    have hq : Q {o} = 0 := (ENNReal.toReal_eq_zero_iff _).mp ho |>.resolve_right (measure_ne_top _ _)
    simp [hAC hq]
  have hn := sum_negativeRelativeEntropyAtom_le (fun o => (P {o}).toReal) (fun o => (Q {o}).toReal)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) (sum_real_finite_atoms Q) hz
  have hp := sum_positiveRelativeEntropyAtom_le (fun o => (P {o}).toReal) (fun o => (Q {o}).toReal)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) (sum_real_finite_atoms Q) hz L.toReal
    (by rw [sum_relativeEntropyAtom_eq_klDiv P Q hAC]; exact ENNReal.toReal_mono hfinite hL)
  have he : (∑ o, |relativeEntropyAtom (P {o}).toReal (Q {o}).toReal|) =
      (∑ o, positiveRelativeEntropyAtom (P {o}).toReal (Q {o}).toReal) +
      ∑ o, negativeRelativeEntropyAtom (P {o}).toReal (Q {o}).toReal := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    dsimp [positiveRelativeEntropyAtom, negativeRelativeEntropyAtom]
    rw [abs_eq_max_neg]
    rcases le_total (relativeEntropyAtom (P {o}).toReal (Q {o}).toReal) 0 with hh | hh
    · rw [max_eq_right (by linarith), max_eq_right hh, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith), max_eq_left hh, max_eq_right (by linarith)]
      ring
  linarith

variable {H : Type*} [MeasurableSpace H]
def slotLogLikelihood (κ η : Kernel H O) (h : H × O) : ℝ :=
  Real.log ((κ h.1 {h.2}).toReal / (η h.1 {h.2}).toReal)

theorem measurable_slotLogLikelihood (κ η : Kernel H O) :
    Measurable (slotLogLikelihood κ η) := by
  apply measurable_from_prod_countable_left
  intro o
  exact Real.measurable_log.comp (((κ.measurable_coe (measurableSet_singleton o)).ennreal_toReal).div
    ((η.measurable_coe (measurableSet_singleton o)).ennreal_toReal))

theorem integrable_slotLogLikelihood (μ : Measure H) [IsProbabilityMeasure μ]
    (κ η : Kernel H O) [IsMarkovKernel κ] [IsMarkovKernel η]
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ h, klDiv (κ h) (η h) ≤ L) :
    Integrable (slotLogLikelihood κ η) (μ ⊗ₘ κ) := by
  apply (Measure.integrable_compProd_iff (measurable_slotLogLikelihood κ η).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun h => integrable_finite_logLikelihood (κ h) _
  · have he (h : H) : (∫ o, ‖slotLogLikelihood κ η (h,o)‖ ∂κ h) =
        ∑ o, |relativeEntropyAtom (κ h {o}).toReal (η h {o}).toReal| := by
      rw [integral_fintype (integrable_finite_logLikelihood (κ h) _)]
      apply Finset.sum_congr rfl
      intro o _
      simp [slotLogLikelihood, relativeEntropyAtom, smul_eq_mul, measureReal_def,
        abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    simp_rw [he]
    have hm : Measurable (fun h => ∑ o, |relativeEntropyAtom (κ h {o}).toReal (η h {o}).toReal|) := by
      apply Finset.measurable_sum
      intro o _
      simpa only [Real.norm_eq_abs, relativeEntropyAtom, Pi.mul_apply, Pi.div_apply, Function.comp_apply] using (((κ.measurable_coe (measurableSet_singleton o)).ennreal_toReal).mul
        (Real.measurable_log.comp (((κ.measurable_coe (measurableSet_singleton o)).ennreal_toReal).div
          ((η.measurable_coe (measurableSet_singleton o)).ennreal_toReal)))).norm
    apply Integrable.of_bound hm.aestronglyMeasurable (L.toReal + 2 * Real.exp (-1))
    apply Filter.Eventually.of_forall
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
    exact sum_abs_relativeEntropyAtom_le (κ h) (η h) L hfinite (hL h)

theorem integral_slotLogLikelihood (μ : Measure H) [IsProbabilityMeasure μ]
    (κ η : Kernel H O) [IsMarkovKernel κ] [IsMarkovKernel η]
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ h, klDiv (κ h) (η h) ≤ L) :
    (∫ h, slotLogLikelihood κ η h ∂(μ ⊗ₘ κ)) =
      ∫ h, (klDiv (κ h) (η h)).toReal ∂μ := by
  rw [Measure.integral_compProd (integrable_slotLogLikelihood μ κ η L hfinite hL)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  dsimp only
  rw [integral_fintype (integrable_finite_logLikelihood (κ h) _)]
  change (∑ o, relativeEntropyAtom (κ h {o}).toReal (η h {o}).toReal) = _
  exact sum_relativeEntropyAtom_eq_klDiv _ _
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top hfinite (hL h))).1
end LocalCertification.Information
