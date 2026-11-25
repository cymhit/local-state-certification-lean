import CertificationGaussian.SphereQuadraticMoments

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian.Consumers
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Arbitrary complex matrix: the actual ψ†Wψ overlap has the exact standard-sphere expectation. -/
theorem standardSphere_quadratic_overlap (W : Matrix I I ℂ) :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
      Complex.normSq (inner ℂ (ψ : EuclideanSpace ℂ I) (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) W ψ))
        ∂canonicalSphereMeasure (EuclideanSpace ℂ I) =
      ((Matrix.trace (W*W.conjTranspose)).re + Complex.normSq (Matrix.trace W)) /
        ((Fintype.card I : ℝ)*((Fintype.card I : ℝ)+1)) := by
  simpa only [sphereQuadraticForm_eq_inner, add_comm] using sphereQuadraticForm_normSq_moment W

/-- The same formula under genuine full-unitary Haar sampling from any fixed unit vector. -/
theorem haar_quadratic_overlap (W : Matrix I I ℂ)
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    ∫ U, Complex.normSq (inner ℂ (complexUnitarySphereAction I U ψ : EuclideanSpace ℂ I)
      (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) W (complexUnitarySphereAction I U ψ)))
        ∂complexUnitaryHaar I =
      ((Matrix.trace (W*W.conjTranspose)).re + Complex.normSq (Matrix.trace W)) /
        ((Fintype.card I : ℝ)*((Fintype.card I : ℝ)+1)) := by
  simpa only [sphereQuadraticForm_eq_inner, add_comm] using haarOrbit_quadratic_normSq_moment W ψ

/-- Traceless unitary overlap, ready for actual Weyl matrices. -/
theorem haar_traceless_unitary_overlap (W : Matrix I I ℂ)
    (hW : W ∈ unitary (Matrix I I ℂ)) (htr : Matrix.trace W = 0)
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    ∫ U, Complex.normSq (inner ℂ (complexUnitarySphereAction I U ψ : EuclideanSpace ℂ I)
      (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) W (complexUnitarySphereAction I U ψ)))
        ∂complexUnitaryHaar I = ((Fintype.card I : ℝ)+1)⁻¹ := by
  rw [haar_quadratic_overlap, htr, show W*W.conjTranspose=1 from hW.2]
  simp only [map_zero, add_zero, Matrix.trace_one, Complex.natCast_re]
  have hD : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The zero matrix has zero overlap on the actual sphere. -/
theorem zero_matrix_overlap :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
      Complex.normSq (sphereQuadraticForm (0 : Matrix I I ℂ) ψ)
        ∂canonicalSphereMeasure (EuclideanSpace ℂ I) = 0 := by
  rw [sphereQuadraticForm_normSq_moment]
  simp

/-- Identity overlap is one in every positive dimension. -/
theorem identity_matrix_overlap :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
      Complex.normSq (sphereQuadraticForm (1 : Matrix I I ℂ) ψ)
        ∂canonicalSphereMeasure (EuclideanSpace ℂ I) = 1 := by
  rw [sphereQuadraticForm_normSq_moment]
  simp only [Matrix.conjTranspose_one, mul_one, Matrix.trace_one, Complex.natCast_re]
  have hD : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD1 : (Fintype.card I : ℝ)+1 ≠ 0 := by positivity
  simp [Complex.normSq_apply]
  field_simp

/-- A nonnormal, non-Hermitian matrix is covered by the general formula. -/
theorem nilpotent_two_overlap :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1,
      Complex.normSq (sphereQuadraticForm !![0,1;0,0] ψ)
        ∂canonicalSphereMeasure (EuclideanSpace ℂ (Fin 2)) = (1:ℝ)/6 := by
  rw [sphereQuadraticForm_normSq_moment]
  norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.normSq_apply]

/-- One complex coordinate, including empty tensor powers, has the exact fourth moment 1. -/
theorem complex_dimension_one_fourth :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ (Fin 1)) 1,
      star (ψ.val 0)*ψ.val 0*star (ψ.val 0)*ψ.val 0
        ∂canonicalSphereMeasure (EuclideanSpace ℂ (Fin 1)) = 1 := by
  simpa using complexSphere_coordinate_fourth_moment (Fin 1) 0 0 0 0

end CertificationGaussian.Consumers
