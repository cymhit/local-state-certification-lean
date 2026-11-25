import CertificationGaussian.SphereComplexMoments
import CertificationGaussian.HaarOrbit

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The actual complex quadratic form ψ†Wψ for an arbitrary complex matrix W. -/
def sphereQuadraticForm (W : Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) : ℂ :=
  ∑ i, ∑ j, star (ψ i)*W i j*ψ j

omit [Nonempty I] in
theorem sphereQuadraticForm_eq_inner (W : Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) :
    sphereQuadraticForm W ψ = inner ℂ ψ (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) W ψ) := by
  simp only [sphereQuadraticForm, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq I] [Nonempty I] in
@[fun_prop] theorem sphereQuadraticForm_continuous (W : Matrix I I ℂ) :
    Continuous (sphereQuadraticForm W) := by
  unfold sphereQuadraticForm
  fun_prop

omit [DecidableEq I] in
theorem complexSphere_integrable_continuous (f : sphere (0 : EuclideanSpace ℂ I) 1 → ℂ)
    (hf : Continuous f) : Integrable f (canonicalSphereMeasure (EuclideanSpace ℂ I)) := by
  let : CompactSpace (sphere (0 : EuclideanSpace ℂ I) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Arbitrary complex quadratic-form mean under the actual canonical sphere probability. -/
theorem sphereQuadraticForm_mean (W : Matrix I I ℂ) :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1, sphereQuadraticForm W ψ
      ∂canonicalSphereMeasure (EuclideanSpace ℂ I) =
      Matrix.trace W/(Fintype.card I : ℂ) := by
  have he (ψ : EuclideanSpace ℂ I) : sphereQuadraticForm W ψ =
      ∑ i, ∑ j, W i j*(star (ψ i)*ψ j) := by
    unfold sphereQuadraticForm
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  simp (disch := (intro _ _; apply complexSphere_integrable_continuous; fun_prop)) only [integral_finsetSum]
  simp_rw [integral_const_mul, complexSphere_coordinate_second_moment,
    ← mul_div_assoc, ← Finset.sum_div]
  simp [Matrix.trace, Matrix.diag]

/-- The fourth-tensor contraction for an arbitrary, possibly nonnormal, complex matrix. -/
theorem sphereQuadraticForm_star_mul_moment (W : Matrix I I ℂ) :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
      star (sphereQuadraticForm W ψ)*sphereQuadraticForm W ψ
        ∂canonicalSphereMeasure (EuclideanSpace ℂ I) =
      (star (Matrix.trace W)*Matrix.trace W + Matrix.trace (W*W.conjTranspose)) /
        ((Fintype.card I : ℂ)*((Fintype.card I : ℂ)+1)) := by
  have he (ψ : EuclideanSpace ℂ I) :
      star (sphereQuadraticForm W ψ)*sphereQuadraticForm W ψ =
      ∑ i, ∑ j, ∑ k, ∑ l, (W i j*star (W k l))*
        (star (ψ i)*ψ j*star (ψ l)*ψ k) := by
    simp only [sphereQuadraticForm, star_sum, star_mul, star_star,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  simp (disch := (intro _ _; apply complexSphere_integrable_continuous; fun_prop)) only [integral_finsetSum]
  simp_rw [integral_const_mul, complexSphere_coordinate_fourth_moment,
    ← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp [mul_add, mul_ite, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_sum, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  simp only [mul_comm]

/-- Actual squared-modulus moment, with the trace expression in real form. -/
theorem sphereQuadraticForm_normSq_moment (W : Matrix I I ℂ) :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
      Complex.normSq (sphereQuadraticForm W ψ) ∂canonicalSphereMeasure (EuclideanSpace ℂ I) =
      (Complex.normSq (Matrix.trace W) + (Matrix.trace (W*W.conjTranspose)).re) /
        ((Fintype.card I : ℝ)*((Fintype.card I : ℝ)+1)) := by
  have h : (∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
      (Complex.normSq (sphereQuadraticForm W ψ):ℂ) ∂canonicalSphereMeasure (EuclideanSpace ℂ I)) =
      ((Complex.normSq (Matrix.trace W):ℂ) + Matrix.trace (W*W.conjTranspose)) /
        ((Fintype.card I : ℂ)*((Fintype.card I : ℂ)+1)) := by
    simpa only [Complex.normSq_eq_conj_mul_self, Complex.star_def] using
      sphereQuadraticForm_star_mul_moment W
  rw [integral_complex_ofReal] at h
  have hden : (Fintype.card I : ℂ)*((Fintype.card I : ℂ)+1) =
      (((Fintype.card I : ℝ)*((Fintype.card I : ℝ)+1):ℝ):ℂ) := by push_cast; rfl
  rw [hden] at h
  simpa only [Complex.ofReal_re, Complex.div_ofReal_re, Complex.add_re] using congrArg Complex.re h

omit [DecidableEq I] [Nonempty I] in
/-- The trace term is the actual Frobenius squared norm, hence a real nonnegative number. -/
theorem trace_mul_conjTranspose_re (W : Matrix I I ℂ) :
    (Matrix.trace (W*W.conjTranspose)).re = ∑ i, ∑ j, Complex.normSq (W i j) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.normSq_apply]

/-- The same quadratic overlap expectation under the genuine full-unitary Haar orbit. -/
theorem haarOrbit_quadratic_normSq_moment (W : Matrix I I ℂ)
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    ∫ U, Complex.normSq (sphereQuadraticForm W (complexUnitarySphereAction I U ψ))
      ∂complexUnitaryHaar I =
      (Complex.normSq (Matrix.trace W) + (Matrix.trace (W*W.conjTranspose)).re) /
        ((Fintype.card I : ℝ)*((Fintype.card I : ℝ)+1)) := by
  have h := sphereQuadraticForm_normSq_moment W
  rw [← complexUnitaryHaar_orbit_map I ψ] at h
  rw [integral_map (complexUnitarySphereAction_continuous I).measurable.of_uncurry_right.aemeasurable
    (show Continuous (fun φ : sphere (0 : EuclideanSpace ℂ I) 1 =>
      Complex.normSq (sphereQuadraticForm W φ)) by fun_prop).aestronglyMeasurable] at h
  exact h

end CertificationGaussian
