import LocalCertification.Information.FiniteHistoryKL
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Information
universe u v
variable {Z : Type u} {O : Type v} [MeasurableSpace Z] [MeasurableSpace O]
  [Fintype O] [MeasurableSingletonClass O]

/-- Recursive form of the common seed measure times counting measure on all slots. -/
def prefixCountingReference (ν : Measure Z) : (m : ℕ) → Measure (SlotHistory Z O m)
  | 0 => ν.map ULift.up
  | m+1 => (prefixCountingReference ν m).prod Measure.count

/-- Actual product of conditional atom masses, including zero and stopped atoms. -/
def prefixProductDensity
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) :
    (m : ℕ) → SlotHistory Z O m → ℝ≥0∞
  | 0 => fun _ => 1
  | m+1 => fun h => prefixProductDensity κ m h.1 * κ m h.1 {h.2}

theorem measurable_prefixProductDensity
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) (m : ℕ) :
    Measurable (prefixProductDensity κ m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    apply (ih.comp measurable_fst).mul
    apply measurable_from_prod_countable_left
    intro o
    exact (κ m).measurable_coe (measurableSet_singleton o)

theorem prefixLaw_withDensity_productDensity (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] (m : ℕ) :
    (prefixCountingReference (O := O) ν m).withDensity (prefixProductDensity κ m) =
      prefixLaw ν κ m := by
  induction m with
  | zero => simp [prefixCountingReference, prefixProductDensity, prefixLaw]
  | succ m ih =>
    apply Measure.ext_of_lintegral
    intro f hf
    change SlotHistory Z O m × Option O → ℝ≥0∞ at f
    change Measurable f at hf
    have hd : Measurable (fun h : SlotHistory Z O m × Option O =>
        prefixProductDensity κ m h.1 * κ m h.1 {h.2}) :=
      measurable_prefixProductDensity κ (m+1)
    change (∫⁻ h, f h ∂((prefixCountingReference ν m).prod Measure.count).withDensity
      (fun h => prefixProductDensity κ m h.1 * κ m h.1 {h.2})) =
      ∫⁻ h, f h ∂(prefixLaw ν κ m ⊗ₘ κ m)
    rw [lintegral_withDensity_eq_lintegral_mul _ hd hf,
      lintegral_prod _ ((hd.mul hf).aemeasurable),
      Measure.lintegral_compProd hf, ← ih,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_prefixProductDensity κ m)
        (hf.lintegral_kernel_prod_right')]
    apply lintegral_congr
    intro h
    simp only [Pi.mul_apply]
    rw [lintegral_fintype, lintegral_fintype, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    simp [prefixProductDensity, mul_assoc, mul_comm, mul_left_comm]

theorem prefixLaw_ac_of_finite_bound_product_density (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)]
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ t h, klDiv (κ t h) (η t h) ≤ L) (m : ℕ) :
    prefixLaw ν κ m ≪ prefixLaw ν η m := by
  induction m with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ m ih =>
    exact ih.compProd (Filter.Eventually.of_forall fun h =>
      (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top hfinite (hL m h))).1)

theorem zero_source_of_zero_denominator_product_density
    (P Q : Measure O) (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : klDiv P Q ≤ L) (o : O) (hzero : Q {o} = 0) :
    P {o} = 0 := by
  exact (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top hfinite hL)).1 hzero
end LocalCertification.Information
