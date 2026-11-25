import LocalCertification.Quantum.MeasurablePOVMRankOne
import CertificationGaussian.MeasurableGaussianFrameBound

/-! # Explicit measurable unit vectors and the actual refinement frame

The measurable spectral basis gives the local frame vectors at every
outcome. Both matrix integration norms are connected through scalar entries.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix CertificationGaussian
open scoped ComplexOrder MatrixOrder
namespace LocalCertification.Quantum.MeasurablePOVM
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Nonempty I]

theorem refinementProjector_eq_vectorRankOne (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    M.refinementProjector s i = vectorRankOne (M.refinementUnitVector s i) (M.refinementUnitVector s i) := by
  rfl

section RefinementReference
variable [MeasurableSpace I] [MeasurableSingletonClass I]

theorem refinementUnitVector_measurable (M : MeasurablePOVM Ω I) :
    Measurable (fun p : Ω × I => M.refinementUnitVector p.1 p.2) :=
  measurable_from_prod_countable_left M.refinementUnitVector_measurable_column

section ElementwiseMean
open scoped Matrix.Norms.Elementwise
local instance povmFrameElementwiseContinuousENorm : ContinuousENorm (Matrix I I ℂ) :=
  SeminormedAddGroup.toContinuousENorm

private def elementwiseEntry (j k : I) : Matrix I I ℂ →L[ℝ] ℂ where
  toFun A := A j k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

private theorem refinementProjector_mean_elementwise (M : MeasurablePOVM Ω I) :
    (∫ p, M.refinementProjector p.1 p.2 ∂M.refinementReference) =
      (Fintype.card I : ℝ)⁻¹ • (1 : Matrix I I ℂ) := by
  have hd : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmean : (∫ p, M.refinementDensity p ∂M.refinementReference) = 1 := by
    simpa only [Measure.restrict_univ, M.refinedPOVM.univ] using
      (M.refinedPOVM_apply MeasurableSet.univ).symm
  calc
    _ = ∫ p, (Fintype.card I : ℝ)⁻¹ • M.refinementDensity p ∂M.refinementReference := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by simp [refinementDensity, smul_smul, hd]
    _ = _ := by rw [integral_smul, hmean]

private theorem refinementProjector_mean_entry (M : MeasurablePOVM Ω I) (j k : I) :
    (∫ p, M.refinementProjector p.1 p.2 j k ∂M.refinementReference) =
      ((Fintype.card I : ℝ)⁻¹ • (1 : Matrix I I ℂ)) j k := by
  have hd : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hi : Integrable (fun p : Ω × I => M.refinementProjector p.1 p.2) M.refinementReference := by
    apply (M.refinementDensity_integrable.smul (Fintype.card I : ℝ)⁻¹).congr
    exact Filter.Eventually.of_forall fun p => by simp [refinementDensity, smul_smul, hd]
  exact ((elementwiseEntry j k).integral_comp_comm hi).trans
    (congrArg (elementwiseEntry j k) (refinementProjector_mean_elementwise M))

end ElementwiseMean

open scoped Matrix.Norms.L2Operator
private def l2Entry (j k : I) : Matrix I I ℂ →L[ℝ] ℂ where
  toFun A := A j k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

/-- The actual normalized first moment, in the matrix topology used by the frame bridge. -/
theorem refinementProjector_mean (M : MeasurablePOVM Ω I) :
    (∫ p, M.refinementProjector p.1 p.2 ∂M.refinementReference) =
      (((1 : ℝ) / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ) := by
  have hi : Integrable (fun p : Ω × I => M.refinementProjector p.1 p.2) M.refinementReference := by
    simp_rw [M.refinementProjector_eq_vectorRankOne]
    exact measurableRankOne_integrable _ _ M.refinementUnitVector_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => M.refinementUnitVector_norm p.1 p.2)
  ext j k
  have he := (l2Entry j k).integral_comp_comm hi
  change (∫ p, M.refinementProjector p.1 p.2 j k ∂M.refinementReference) =
    (∫ p, M.refinementProjector p.1 p.2 ∂M.refinementReference) j k at he
  rw [← he, refinementProjector_mean_entry]
  simp only [one_div, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Every actual measurable POVM refinement has the genuine local frame bound. -/
theorem refinementFrame_norm_le (M : MeasurablePOVM Ω I) :
    ‖integralMatrixFrame M.refinementReference (fun p => M.refinementProjector p.1 p.2)‖ ≤
      1 / (Fintype.card I : ℝ) := by
  unfold integralMatrixFrame
  simp_rw [M.refinementProjector_eq_vectorRankOne]
  apply measurableRankOneFrame_norm_le _ _ M.refinementUnitVector_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => M.refinementUnitVector_norm p.1 p.2)
    (by positivity : 0 ≤ (1 : ℝ) / (Fintype.card I : ℝ))
  simpa only [M.refinementProjector_eq_vectorRankOne] using M.refinementProjector_mean

/-- The zero-radius Gaussian variance bound for the actual refined reference probability. -/
theorem refinementGaussian_zeroRadius_variance (M : MeasurablePOVM Ω I) :
    ProbabilityTheory.variance (measurableQuadraticEnsemble M.refinementReference
      (fun p => M.refinementProjector p.1 p.2)) (pairedGaussian I) ≤ 8 / (Fintype.card I : ℝ) := by
  simp_rw [M.refinementProjector_eq_vectorRankOne]
  apply measurableRankOneGaussian_zeroRadius_variance _ _ M.refinementUnitVector_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => M.refinementUnitVector_norm p.1 p.2)
  simpa only [M.refinementProjector_eq_vectorRankOne] using M.refinementProjector_mean

end RefinementReference
end LocalCertification.Quantum.MeasurablePOVM
