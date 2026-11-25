import CertificationGaussian.GaussianMatrixExpectation
import CertificationGaussian.MatrixHermitianDilation

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I R C : Type*} [Fintype I] [DecidableEq I]
  [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- The actual two covariance matrices of a rectangular complex coefficient family. -/
def gaussianLeftCovariance (H : I → Matrix R C ℂ) : Matrix R R ℂ := ∑ i, H i*(H i)ᴴ

def gaussianRightCovariance (H : I → Matrix R C ℂ) : Matrix C C ℂ := ∑ i, (H i)ᴴ*H i

omit [DecidableEq I] [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
/-- Real Gaussian scalar multiplication commutes with Hermitian dilation. -/
theorem hermitianDilation_gaussianMatrixSeries (H : I → Matrix R C ℂ) (x : I → ℝ) :
    hermitianDilation (gaussianMatrixSeries H x) =
      gaussianMatrixSeries (fun i => hermitianDilation (H i)) x := by
  ext (a | a) (b | b) <;>
    simp [hermitianDilation, gaussianMatrixSeries, Matrix.sum_apply,
      Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]

omit [DecidableEq I] in
/-- The sum of squared dilations is the genuine block diagonal of the two covariance matrices. -/
theorem hermitianDilation_gaussianCovariance (H : I → Matrix R C ℂ) :
    gaussianMatrixCovariance (fun i => hermitianDilation (H i)) =
      Matrix.fromBlocks (gaussianLeftCovariance H) 0 0 (gaussianRightCovariance H) := by
  unfold gaussianMatrixCovariance
  simp_rw [hermitianDilation_sq]
  ext (a | a) (b | b) <;>
    simp [gaussianLeftCovariance, gaussianRightCovariance, Matrix.sum_apply]

omit [DecidableEq I] in
theorem hermitianDilation_gaussian_norm (H : I → Matrix R C ℂ) (x : I → ℝ) :
    ‖Matrix.toEuclideanCLM (n := R ⊕ C) (𝕜 := ℂ)
      (gaussianMatrixSeries (fun i => hermitianDilation (H i)) x)‖ =
      ‖rectangularEuclideanCLM (gaussianMatrixSeries H x)‖ := by
  rw [← hermitianDilation_gaussianMatrixSeries, Matrix.l2_opNorm_toEuclideanCLM,
    hermitianDilation_norm, rectangularEuclideanCLM_norm]

omit [DecidableEq I] in
theorem hermitianDilation_covariance_norm (H : I → Matrix R C ℂ) :
    ‖Matrix.toEuclideanCLM (n := R ⊕ C) (𝕜 := ℂ)
      (gaussianMatrixCovariance (fun i => hermitianDilation (H i)))‖ =
      max ‖Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ) (gaussianLeftCovariance H)‖
        ‖Matrix.toEuclideanCLM (n := C) (𝕜 := ℂ) (gaussianRightCovariance H)‖ := by
  rw [hermitianDilation_gaussianCovariance, Matrix.l2_opNorm_toEuclideanCLM,
    matrix_l2_blockDiagonal_norm, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM]

omit [DecidableEq I] in
/-- Every finite Lp norm exists for an arbitrary rectangular complex Gaussian matrix series. -/
theorem rectangularGaussian_opNorm_memLp (H : I → Matrix R C ℂ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => ‖rectangularEuclideanCLM (gaussianMatrixSeries H x)‖)
      p (realGaussianProduct I) := by
  have h := gaussianMatrixSeries_opNorm_memLp (fun i => hermitianDilation (H i))
    (fun i => hermitianDilation_isHermitian (H i)) p hp
  simpa only [hermitianDilation_gaussian_norm] using h

private theorem sqrt_max_eq (a b : ℝ) : Real.sqrt (max a b) = max (Real.sqrt a) (Real.sqrt b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.sqrt_le_sqrt h)]
  · rw [max_eq_left h, max_eq_left (Real.sqrt_le_sqrt h)]

/-- The first-order rectangular Gaussian matrix inequality with one absolute constant.
Both covariance orientations are retained; the dimensions and the Gaussian family may be empty. -/
theorem rectangularGaussian_expectation_bound (H : I → Matrix R C ℂ) :
    ∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries H x)‖ ∂realGaussianProduct I ≤
      gaussianMatrixExpectationConstant * Real.sqrt (Real.log (2*((Fintype.card R:ℝ)+Fintype.card C))) *
        max (Real.sqrt ‖Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ) (gaussianLeftCovariance H)‖)
          (Real.sqrt ‖Matrix.toEuclideanCLM (n := C) (𝕜 := ℂ) (gaussianRightCovariance H)‖) := by
  have h := gaussianMatrixSeries_expectation_bound (fun i => hermitianDilation (H i))
    (fun i => hermitianDilation_isHermitian (H i))
  simp only [hermitianDilation_gaussian_norm, hermitianDilation_covariance_norm,
    sqrt_max_eq, Fintype.card_sum, Nat.cast_add] at h
  exact h

end CertificationGaussian
