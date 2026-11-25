import CertificationGaussian.SpherePolar

noncomputable section
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
namespace CertificationGaussian

section Isometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual restriction of a real linear isometry to the two standard unit spheres. -/
def sphereIsometry (e : E ≃ₗᵢ[ℝ] F) : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 :=
  e.toHomeomorph.subtype (fun x => by
    change x ∈ sphere (0 : E) 1 ↔ e x ∈ sphere (0 : F) 1
    simp only [mem_sphere_zero_iff_norm, e.norm_map])

@[simp] theorem sphereIsometry_coe (e : E ≃ₗᵢ[ℝ] F) (x : sphere (0 : E) 1) :
    (sphereIsometry e x : F) = e x := rfl

/-- The cones defining standard area are carried by the same real isometry. -/
theorem sphereIsometry_cone_preimage (e : E ≃ₗᵢ[ℝ] F) (s : Set (sphere (0 : F) 1)) :
    e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereIsometry e) ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, he⟩
    refine ⟨r, hr, ((sphereIsometry e).symm u : E), ?_, ?_⟩
    · exact ⟨(sphereIsometry e).symm u, by simpa using hu, rfl⟩
    · apply e.injective
      simpa only [e.map_smul, ← sphereIsometry_coe, Homeomorph.apply_symm_apply] using he
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨r, hr, e u, ⟨sphereIsometry e u, hu, rfl⟩, (e.map_smul r u).symm⟩

/-- Positive radial scaling cancels pointwise, including the chosen value at zero. -/
theorem sphereDirection_pos_smul (e₀ : sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) (x : E) :
    sphereDirection e₀ (r • x) = sphereDirection e₀ x := by
  apply Subtype.ext
  by_cases hx : x = 0
  · simp [sphereDirection_coe, hx]
  · have hrx : r • x ≠ 0 := smul_ne_zero hr.ne' hx
    simp only [sphereDirection_coe, ite_eq_right hx, ite_eq_right hrx, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, mul_inv, smul_smul]
    congr 1
    field_simp

/-- Direction commutes with the actual sphere restriction of a real isometry. -/
theorem sphereDirection_isometry (e : E ≃ₗᵢ[ℝ] F) (e₀ : sphere (0 : E) 1) (x : E) :
    sphereDirection (sphereIsometry e e₀) (e x) = sphereIsometry e (sphereDirection e₀ x) := by
  apply Subtype.ext
  by_cases hx : x = 0
  · simp [sphereDirection_coe, hx]
  · have hex : e x ≠ 0 := by simpa using hx
    simp only [sphereDirection_coe, ite_eq_right hx, ite_eq_right hex, sphereIsometry_coe, e.norm_map]
    exact (e.map_smul _ _).symm

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Canonical standard area is transported to canonical standard area, not merely to an unnamed image. -/
theorem sphereIsometry_area_map (e : E ≃ₗᵢ[ℝ] F) :
    ((volume : Measure E).toSphere).map (sphereIsometry e) = (volume : Measure F).toSphere := by
  ext s hs
  rw [Measure.map_apply (sphereIsometry e).measurable hs,
    Measure.toSphere_apply' _ ((sphereIsometry e).measurable hs), Measure.toSphere_apply' _ hs]
  rw [e.toLinearEquiv.finrank_eq, ← sphereIsometry_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

/-- Standard sphere probability defined solely from canonical volume. -/
def canonicalSphereMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure (sphere (0 : E) 1) :=
  ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere

theorem sphereIsometry_area_mass (e : E ≃ₗᵢ[ℝ] F) :
    (volume : Measure E).toSphere univ = (volume : Measure F).toSphere univ := by
  have h := congrArg (fun μ : Measure (sphere (0 : F) 1) => μ univ) (sphereIsometry_area_map e)
  simpa only [Measure.map_apply (sphereIsometry e).measurable MeasurableSet.univ, preimage_univ] using h

theorem sphereIsometry_canonical_map (e : E ≃ₗᵢ[ℝ] F) :
    (canonicalSphereMeasure E).map (sphereIsometry e) = canonicalSphereMeasure F := by
  rw [canonicalSphereMeasure, Measure.map_smul _ (sphereIsometry e).measurable.aemeasurable,
    sphereIsometry_area_map e, sphereIsometry_area_mass e]
  rfl

instance canonicalSphereMeasure_probability [Nontrivial E] : IsProbabilityMeasure (canonicalSphereMeasure E) where
  measure_univ := by
    rw [canonicalSphereMeasure, Measure.smul_apply, smul_eq_mul]
    apply ENNReal.inv_mul_cancel
    · exact Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (volume : Measure E))
    · finiteness

/-- Transfer of the proved real-coordinate direction law to the canonical area of any isometric space. -/
theorem stdGaussian_direction_map_of_isometry (I : Type*) [Fintype I] [Nonempty I]
    (e : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] E) (e₀ : sphere (0 : E) 1) :
    (stdGaussian E).map (sphereDirection e₀) = canonicalSphereMeasure E := by
  let a := (sphereIsometry e).symm e₀
  have he : sphereDirection e₀ ∘ e = sphereIsometry e ∘ sphereDirection a := by
    funext x
    have h := sphereDirection_isometry e a x
    simpa only [a, Homeomorph.apply_symm_apply, Function.comp_apply] using h
  calc
    _ = ((stdGaussian (EuclideanSpace ℝ I)).map e).map (sphereDirection e₀) := by
      rw [stdGaussian_map]
    _ = ((stdGaussian (EuclideanSpace ℝ I)).map (sphereDirection a)).map (sphereIsometry e) := by
      rw [Measure.map_map (sphereDirection_measurable e₀) e.continuous.measurable, he,
        ← Measure.map_map (sphereIsometry e).measurable (sphereDirection_measurable a)]
    _ = (standardSphereMeasure I).map (sphereIsometry e) := by rw [stdGaussian_direction_map]
    _ = _ := sphereIsometry_canonical_map e

end Isometry

variable (I : Type*) [Fintype I] [Nonempty I]

/-- The complex Hilbert sphere carries its own canonical normalized area, identified by real isometry. -/
theorem complexStdGaussian_direction_map (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    (stdGaussian (EuclideanSpace ℂ I)).map (sphereDirection e₀) =
      canonicalSphereMeasure (EuclideanSpace ℂ I) :=
  stdGaussian_direction_map_of_isometry (Fin 2 × I) (complexRealIsometry I) e₀

theorem complexStdGaussian_zero_null :
    stdGaussian (EuclideanSpace ℂ I) {0} = 0 := by
  rw [← stdGaussian_map (complexRealIsometry I),
    Measure.map_apply (complexRealIsometry I).continuous.measurable (measurableSet_singleton _)]
  have he : (complexRealIsometry I) ⁻¹' ({0} : Set (EuclideanSpace ℂ I)) = {0} := by
    ext x
    simp
  rw [he, stdGaussian_zero_null]

theorem complexGaussianLift_zero_null :
    pairedGaussian I {x | complexGaussianLift I x = 0} = 0 := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℂ I) => μ {0}) (complexGaussianLift_map I)
  rw [Measure.map_apply (complexGaussianLift_continuous I).measurable (measurableSet_singleton _),
    Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
  have he : (fun z : EuclideanSpace ℂ I => (Real.sqrt 2)⁻¹ • z) ⁻¹' {0} = {0} := by
    ext z
    simp [smul_eq_zero, show (Real.sqrt 2)⁻¹ ≠ 0 by positivity]
  rw [he, complexStdGaussian_zero_null] at h
  exact h

/-- Actual paired coordinates divided by sqrt(2), normalized to a unit vector, have standard sphere law. -/
theorem complexGaussian_direction_map (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    (pairedGaussian I).map (fun x => sphereDirection e₀ (complexGaussianLift I x)) =
      canonicalSphereMeasure (EuclideanSpace ℂ I) := by
  change (pairedGaussian I).map (sphereDirection e₀ ∘ complexGaussianLift I) = _
  rw [← Measure.map_map (sphereDirection_measurable e₀)
    (complexGaussianLift_continuous I).measurable, complexGaussianLift_map,
    Measure.map_map (sphereDirection_measurable e₀) (by fun_prop)]
  have he : sphereDirection e₀ ∘ (fun z : EuclideanSpace ℂ I => (Real.sqrt 2)⁻¹ • z) = sphereDirection e₀ := by
    funext z
    exact sphereDirection_pos_smul e₀ (by positivity) z
  rw [he, complexStdGaussian_direction_map]

end CertificationGaussian
