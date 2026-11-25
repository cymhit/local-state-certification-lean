import CertificationGaussian.ComplexMeasurableFrame
import CertificationGaussian.UnitaryFrobeniusPacking

/-! # Canonical measurable frame witnesses and finite operator nets

Every original measurable unit-vector ensemble is pushed to the same unit
sphere. The pushforward preserves its actual first moment and actual complex
frame. Net centers remain in the set of frames with such probability witnesses;
no finite representation of the original outcome measure is assumed.
-/

noncomputable section
open MeasureTheory Metric Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev ComplexMatrixFrameSpace (I : Type*) [Fintype I] :=
  EuclideanSpace ℂ (I × I) →L[ℂ] EuclideanSpace ℂ (I × I)

def sphereProjector (ψ : sphere (0 : EuclideanSpace ℂ I) 1) : Matrix I I ℂ :=
  vectorRankOne ψ.val ψ.val

omit [DecidableEq I] in
theorem sphereProjector_continuous : Continuous (sphereProjector (I := I)) := by
  unfold sphereProjector vectorRankOne
  fun_prop

private theorem complexRankOne_continuous {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : Continuous (fun x : E => InnerProductSpace.rankOne ℂ x x) := by
  change Continuous (fun x : E => (ContinuousLinearMap.smulRightL ℂ E E) (innerSL ℂ x) x)
  exact ((ContinuousLinearMap.smulRightL ℂ E E).continuous.comp (innerSL ℂ).continuous).clm_apply continuous_id

omit [DecidableEq I] in
theorem sphereProjector_frame_continuous : Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 =>
    InnerProductSpace.rankOne ℂ (matrixHilbertSchmidt (sphereProjector ψ))
      (matrixHilbertSchmidt (sphereProjector ψ))) := by
  apply complexRankOne_continuous.comp
  unfold matrixHilbertSchmidt sphereProjector vectorRankOne
  fun_prop

omit [DecidableEq I] in
def unitEnsembleSphereMap {Ω : Type*} (u : Ω → EuclideanSpace ℂ I)
    (hu : ∀ s, ‖u s‖ = 1) : Ω → sphere (0 : EuclideanSpace ℂ I) 1 :=
  fun s => ⟨u s, mem_sphere_zero_iff_norm.mpr (hu s)⟩

omit [DecidableEq I] in
theorem unitEnsembleSphereMap_measurable {Ω : Type*} [MeasurableSpace Ω]
    (u : Ω → EuclideanSpace ℂ I) (hm : Measurable u) (hu : ∀ s, ‖u s‖ = 1) :
    Measurable (unitEnsembleSphereMap u hu) := hm.subtype_mk

theorem sphereProjector_map_integral {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (u : Ω → EuclideanSpace ℂ I) (hm : Measurable u) (hu : ∀ s, ‖u s‖ = 1) :
    (∫ ψ, sphereProjector ψ ∂ν.map (unitEnsembleSphereMap u hu)) =
      ∫ s, vectorRankOne (u s) (u s) ∂ν := by
  rw [integral_map_of_stronglyMeasurable (unitEnsembleSphereMap_measurable u hm hu)
    sphereProjector_continuous.stronglyMeasurable]
  rfl

omit [DecidableEq I] in
theorem sphereProjector_map_frame {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (u : Ω → EuclideanSpace ℂ I) (hm : Measurable u) (hu : ∀ s, ‖u s‖ = 1) :
    integralComplexMatrixFrame (ν.map (unitEnsembleSphereMap u hu)) sphereProjector =
      integralComplexMatrixFrame ν (fun s => vectorRankOne (u s) (u s)) := by
  unfold integralComplexMatrixFrame integralComplexHilbertFrame
  rw [integral_map_of_stronglyMeasurable (unitEnsembleSphereMap_measurable u hm hu)
    sphereProjector_frame_continuous.stronglyMeasurable]
  rfl

/-- A canonical actual probability witness, preserving the original frame. -/
theorem exists_canonicalRankOneFrame {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (u : Ω → EuclideanSpace ℂ I) (hm : Measurable u) (hu : ∀ s, ‖u s‖ = 1)
    (hmean : (∫ s, vectorRankOne (u s) (u s) ∂ν) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) :
    ∃ η : Measure (sphere (0 : EuclideanSpace ℂ I) 1), IsProbabilityMeasure η ∧
      (∫ ψ, vectorRankOne ψ.val ψ.val ∂η) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ) ∧
      integralComplexMatrixFrame η (fun ψ => vectorRankOne ψ.val ψ.val) =
        integralComplexMatrixFrame ν (fun s => vectorRankOne (u s) (u s)) := by
  refine ⟨ν.map (unitEnsembleSphereMap u hu), ?_, ?_, sphereProjector_map_frame ν u hm hu⟩
  · exact (Measure.isProbabilityMeasure_map_iff
      (unitEnsembleSphereMap_measurable u hm hu).aemeasurable).mpr inferInstance
  · exact (sphereProjector_map_integral ν u hm hu).trans hmean

/-- These are exactly frames with actual canonical probability witnesses. -/
def canonicalRankOneFrames : Set (ComplexMatrixFrameSpace I) :=
  {T | ∃ η : Measure (sphere (0 : EuclideanSpace ℂ I) 1), IsProbabilityMeasure η ∧
    (∫ ψ, vectorRankOne ψ.val ψ.val ∂η) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ) ∧
    T = integralComplexMatrixFrame η (fun ψ => vectorRankOne ψ.val ψ.val)}

theorem measurableRankOneFrame_mem_canonical {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (u : Ω → EuclideanSpace ℂ I) (hm : Measurable u) (hu : ∀ s, ‖u s‖ = 1)
    (hmean : (∫ s, vectorRankOne (u s) (u s) ∂ν) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) :
    integralComplexMatrixFrame ν (fun s => vectorRankOne (u s) (u s)) ∈ canonicalRankOneFrames := by
  obtain ⟨η, hη, hmeanη, hframe⟩ := exists_canonicalRankOneFrame ν u hm hu hmean
  exact ⟨η, hη, hmeanη, hframe.symm⟩

theorem canonicalRankOneFrames_norm_le (T : canonicalRankOneFrames (I := I)) :
    ‖T.val‖ ≤ (Fintype.card I : ℝ)⁻¹ := by
  obtain ⟨η, hη, hmean, heq⟩ := T.property
  let := hη
  rw [heq]
  apply measurableRankOneComplexFrame_norm_le η (fun ψ => ψ.val)
    continuous_subtype_val.measurable.aestronglyMeasurable
    (ae_of_all _ fun ψ => mem_sphere_zero_iff_norm.mp ψ.property) (by positivity)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using hmean

omit [DecidableEq I] in
theorem complexMatrixFrameSpace_real_dimension :
    Module.finrank ℝ (ComplexMatrixFrameSpace I) = 2*(Fintype.card I)^4 := by
  let E := EuclideanSpace ℂ (I × I)
  have he : Module.finrank ℂ (E →L[ℂ] E) = Module.finrank ℂ (E →ₗ[ℂ] E) :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℂ] E) ≃ₗ[ℂ] (E →L[ℂ] E)).finrank_eq.symm
  change Module.finrank ℝ (E →L[ℂ] E) = _
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, he,
    Module.finrank_linearMap]
  simp only [E, finrank_euclideanSpace, Fintype.card_prod]
  ring

/-- Actual centers and their probability witnesses are retained by the net. -/
theorem canonicalRankOneFrames_exists_net (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (canonicalRankOneFrames (I := I)),
      (∀ T : canonicalRankOneFrames (I := I), ∃ U ∈ s, ‖T.val-U.val‖ ≤ ε) ∧
      (s.card : ℝ) ≤ (1+2*(Fintype.card I : ℝ)⁻¹/ε)^(2*(Fintype.card I)^4) := by
  obtain ⟨s, _, hcover, hcard⟩ := exists_maximal_separated_net
    (fun T : canonicalRankOneFrames (I := I) => T.val) Subtype.val_injective
    (inv_nonneg.mpr (Nat.cast_nonneg _)) hε canonicalRankOneFrames_norm_le
  exact ⟨s, hcover, by simpa only [complexMatrixFrameSpace_real_dimension] using hcard⟩

theorem canonicalRankOneFrames_isCompact_closure :
    IsCompact (closure (canonicalRankOneFrames (I := I))) := by
  apply (isCompact_closedBall (0 : ComplexMatrixFrameSpace I) (Fintype.card I : ℝ)⁻¹).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro T hT
  simpa only [mem_closedBall, dist_zero_right] using canonicalRankOneFrames_norm_le ⟨T, hT⟩

/-- The same actual centers cover the compact closure; no limiting center is substituted. -/
theorem canonicalRankOneFrames_exists_closure_net (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (canonicalRankOneFrames (I := I)),
      (∀ T ∈ closure (canonicalRankOneFrames (I := I)), ∃ U ∈ s, ‖T-U.val‖ ≤ ε) ∧
      (s.card : ℝ) ≤ (1+2*(Fintype.card I : ℝ)⁻¹/ε)^(2*(Fintype.card I)^4) := by
  obtain ⟨s, hcover, hcard⟩ := canonicalRankOneFrames_exists_net (I := I) ε hε
  let C : Set (ComplexMatrixFrameSpace I) := ⋃ U ∈ s, {T | ‖T-U.val‖ ≤ ε}
  have hclosed : IsClosed C := by
    apply isClosed_biUnion_finset
    intro U _
    exact isClosed_le (continuous_id.sub continuous_const).norm continuous_const
  have hsub : canonicalRankOneFrames ⊆ C := by
    intro T hT
    obtain ⟨U, hU, hd⟩ := hcover ⟨T, hT⟩
    exact Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨hU, hd⟩⟩
  refine ⟨s, ?_, hcard⟩
  intro T hT
  obtain ⟨U, hU⟩ := Set.mem_iUnion.mp (closure_minimal hsub hclosed hT)
  obtain ⟨hUs, hd⟩ := Set.mem_iUnion.mp hU
  exact ⟨U, hUs, hd⟩

end CertificationGaussian
