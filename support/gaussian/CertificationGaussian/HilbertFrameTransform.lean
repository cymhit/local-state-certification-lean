import CertificationGaussian.MeasurableQuadraticFrame

/-! # Congruence of genuine Bochner frames

The reference probability and outcome space are arbitrary. Integrability of the
transformed frame is derived from the actual bounded linear map and ensemble.
-/

noncomputable section
open MeasureTheory
namespace CertificationGaussian
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

theorem integralHilbertFrame_map (V : Ω → E) (hV : AEStronglyMeasurable V ν)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (R : E →L[ℝ] E) :
    integralHilbertFrame ν (fun s => R (V s)) =
      R.comp ((integralHilbertFrame ν V).comp (ContinuousLinearMap.adjoint R)) := by
  have hRV : AEStronglyMeasurable (fun s => R (V s)) ν := R.continuous.comp_aestronglyMeasurable hV
  have hRb : ∀ᵐ s ∂ν, ‖R (V s)‖ ≤ ‖R‖ * K := by
    filter_upwards [hbound] with s hs
    exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [integralHilbertFrame_inner ν _ hRV (mul_nonneg (norm_nonneg _) hK) hRb]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_right,
    integralHilbertFrame_inner ν V hV hK hbound]
  simp only [ContinuousLinearMap.adjoint_inner_right]

theorem integralHilbertFrame_map_norm (V : Ω → E) (hV : AEStronglyMeasurable V ν)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (R : E →L[ℝ] E) :
    ‖integralHilbertFrame ν (fun s => R (V s))‖ ≤ ‖R‖ ^ 2 * ‖integralHilbertFrame ν V‖ := by
  rw [integralHilbertFrame_map ν V hV hK hbound R]
  calc
    _ ≤ ‖R‖ * ‖(integralHilbertFrame ν V).comp (ContinuousLinearMap.adjoint R)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖R‖ * (‖integralHilbertFrame ν V‖ * ‖ContinuousLinearMap.adjoint R‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by simp only [LinearIsometryEquiv.norm_map]; ring

/-- Pointwise nonnegative quadratic forms for the actual integral frame. -/
theorem integralHilbertFrame_nonneg (V : Ω → E) (hV : AEStronglyMeasurable V ν)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (x : E) :
    0 ≤ inner ℝ (integralHilbertFrame ν V x) x := by
  rw [integralHilbertFrame_inner ν V hV hK hbound]
  exact integral_nonneg fun s => mul_self_nonneg _

/-- Self-adjointness follows from the genuine real frame integral. -/
theorem integralHilbertFrame_adjoint (V : Ω → E) (hV : AEStronglyMeasurable V ν)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) :
    ContinuousLinearMap.adjoint (integralHilbertFrame ν V) = integralHilbertFrame ν V := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  conv_lhs => rw [real_inner_comm]
  rw [integralHilbertFrame_inner ν V hV hK hbound,
    integralHilbertFrame_inner ν V hV hK hbound]
  simp only [mul_comm]

end CertificationGaussian
