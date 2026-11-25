import LocalCertification.Quantum.MeasurableDualResidual
import LocalCertification.Quantum.MeasurablePOVMProductInformation

/-! Actual original-product information bounds from the fixed finite-dual kernel.
The only remaining analytic input for a uniform rate is a bound on the displayed
centered kernel integral; no concentration assertion is assumed or proved here. -/

open MeasureTheory Matrix InformationTheory LocalCertification.Extremal
open scoped ENNReal ComplexOrder
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum
variable {d n r : ℕ} [NeZero d] {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- The centered kernel integral under the refined product measurement law. -/
def dualResidualQuadratic (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) : ℝ :=
  (d : ℝ)^(2*n) *
    ∫ s, (((ψ.state.matrix - (quditMaximallyMixed d n).matrix) *
      CertificationGaussian.cardinalityProjectorKernel
        (fun i => (M i).refinementProjector (s i).1 (s i).2)
        (residualRadii c) (residualWeight d c)).trace.re)^2
      ∂MeasurablePOVM.productRefinementReference M

theorem dualResidualQuadratic_nonneg (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) : 0 ≤ dualResidualQuadratic c ψ M :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (integral_nonneg (fun _ => sq_nonneg _))

/-- Squaring and integrating the literal original-dual readout retains its exact coefficient. -/
theorem dualStates_refined_difference_sq_integral (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (∫ s, (MeasurablePOVM.productRefinedBornDensity M (dualHighState hd c ψ hN) s -
      MeasurablePOVM.productRefinedBornDensity M (dualLowState hd c ψ hN) s)^2
        ∂MeasurablePOVM.productRefinementReference M) =
      (c.infinityWeight / dualNormalization ((d : ℝ)+1) r)^2 * dualResidualQuadratic c ψ M := by
  have hp : ((d : ℝ)^n)^2 = (d : ℝ)^(2*n) := by rw [← pow_mul, Nat.mul_comm]
  calc
    _ = ∫ s, (c.infinityWeight / dualNormalization ((d : ℝ)+1) r)^2 *
        ((d : ℝ)^(2*n) * (((ψ.state.matrix - (quditMaximallyMixed d n).matrix) *
          CertificationGaussian.cardinalityProjectorKernel
            (fun i => (M i).refinementProjector (s i).1 (s i).2)
            (residualRadii c) (residualWeight d c)).trace.re)^2)
          ∂MeasurablePOVM.productRefinementReference M := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by
        dsimp only
        rw [dualStates_refinedBornDensity_difference hd c ψ hN M s, ← hp]
        ring)
    _ = _ := by rw [integral_const_mul, integral_const_mul]; rfl

/-- The same quadratic quantity applies to the opposite ordering of the actual states. -/
theorem dualStates_refined_difference_sq_integral_reverse (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (∫ s, (MeasurablePOVM.productRefinedBornDensity M (dualLowState hd c ψ hN) s -
      MeasurablePOVM.productRefinedBornDensity M (dualHighState hd c ψ hN) s)^2
        ∂MeasurablePOVM.productRefinementReference M) =
      (c.infinityWeight / dualNormalization ((d : ℝ)+1) r)^2 * dualResidualQuadratic c ψ M := by
  calc
    _ = ∫ s, (MeasurablePOVM.productRefinedBornDensity M (dualHighState hd c ψ hN) s -
        MeasurablePOVM.productRefinedBornDensity M (dualLowState hd c ψ hN) s)^2
          ∂MeasurablePOVM.productRefinementReference M := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => by ring)
    _ = _ := dualStates_refined_difference_sq_integral hd c ψ hN M

/-- The original product measurement's reference distance is bounded by the actual kernel integral. -/
theorem dualStates_product_referenceL2_sq_le (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (∫ s, ((MeasurablePOVM.product M).bornDensity (dualHighState hd c ψ hN) s -
      (MeasurablePOVM.product M).bornDensity (dualLowState hd c ψ hN) s)^2
        ∂(MeasurablePOVM.product M).traceReference) ≤
      (c.infinityWeight / dualNormalization ((d : ℝ)+1) r)^2 * dualResidualQuadratic c ψ M := by
  have h := MeasurablePOVM.product_referenceL2_sq_le_localRefinement M
    (dualHighState hd c ψ hN) (dualLowState hd c ψ hN)
  rwa [dualStates_refined_difference_sq_integral hd c ψ hN M] at h

/-- Even auxiliary degree puts the actual uniform denominator component in the high state. -/
theorem dualStates_product_klDiv_le_even (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) (hr : Even r) :
    klDiv ((MeasurablePOVM.product M).born (dualLowState hd c ψ hN))
      ((MeasurablePOVM.product M).born (dualHighState hd c ψ hN)) ≤
      ENNReal.ofReal ((uniformComponentWeight c)⁻¹ *
        (c.infinityWeight / dualNormalization ((d : ℝ)+1) r)^2 * dualResidualQuadratic c ψ M) := by
  have hfloor := dualHighState_uniform_floor_even hd c ψ hN hr
  have h := MeasurablePOVM.product_born_klDiv_le_refined_sq M
    (dualLowState hd c ψ hN) (dualHighState hd c ψ hN) (uniformComponentWeight c)
    (uniformComponentWeight_pos (qudit_parameter_gt_one hd) c) hfloor
  rw [dualStates_refined_difference_sq_integral_reverse hd c ψ hN M] at h
  simpa only [mul_assoc] using h

/-- Odd auxiliary degree puts the actual uniform denominator component in the low state. -/
theorem dualStates_product_klDiv_le_odd (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) (hr : Odd r) :
    klDiv ((MeasurablePOVM.product M).born (dualHighState hd c ψ hN))
      ((MeasurablePOVM.product M).born (dualLowState hd c ψ hN)) ≤
      ENNReal.ofReal ((uniformComponentWeight c)⁻¹ *
        (c.infinityWeight / dualNormalization ((d : ℝ)+1) r)^2 * dualResidualQuadratic c ψ M) := by
  have hfloor := dualLowState_uniform_floor_odd hd c ψ hN hr
  have h := MeasurablePOVM.product_born_klDiv_le_refined_sq M
    (dualHighState hd c ψ hN) (dualLowState hd c ψ hN) (uniformComponentWeight c)
    (uniformComponentWeight_pos (qudit_parameter_gt_one hd) c) hfloor
  rw [dualStates_refined_difference_sq_integral hd c ψ hN M] at h
  simpa only [mul_assoc] using h

end LocalCertification.Quantum
