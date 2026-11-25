import LocalCertification.Quantum.Boundary
import CertificationGaussian.Consumers.Moments

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory GaussianHilbert
noncomputable section
namespace LocalCertification.Quantum

/-- The QIT tensor-label basis transported into the adapter's sole function-label index. -/
def tensorBasis (d n : ℕ)
    (U : Matrix (QIT.TensorPower (Fin d) n) (QIT.TensorPower (Fin d) n) ℂ) :
    Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ :=
  Matrix.reindex (quditTensorEquiv d n) (quditTensorEquiv d n) U

theorem tensorBasis_apply (d n : ℕ)
    (U : Matrix (QIT.TensorPower (Fin d) n) (QIT.TensorPower (Fin d) n) ℂ)
    (i j : CertificationGaussian.QuditIndex d n) :
    tensorBasis d n U i j = U ((quditTensorEquiv d n).symm i) ((quditTensorEquiv d n).symm j) := rfl

theorem tensorBasis_l2_norm (d n : ℕ)
    (U : Matrix (QIT.TensorPower (Fin d) n) (QIT.TensorPower (Fin d) n) ℂ) :
    ‖tensorBasis d n U‖ = ‖U‖ := matrix_reindex_l2_opNorm _ _ U

/-- General actual-qudit consumer: no chaos-membership, mean, variance, or norm premise. -/
theorem qudit_tensor_gaussian_moment (d n : ℕ) (J : Finset ℕ) (θ : ℕ → ℝ)
    (U : Matrix (QIT.TensorPower (Fin d) n) (QIT.TensorPower (Fin d) n) ℂ)
    (p : ℝ) (hp : 2 ≤ p) :
    MemLp (CertificationGaussian.quditStandardQuartic d n J θ (tensorBasis d n U))
      (ENNReal.ofReal p) (stdGaussianFin (2*d^n)) ∧
    eLpNorm (CertificationGaussian.quditStandardQuartic d n J θ (tensorBasis d n U))
      (ENNReal.ofReal p) (stdGaussianFin (2*d^n)) ≤
      ENNReal.ofReal (5*(p-1)^2) *
        eLpNorm (CertificationGaussian.quditStandardQuartic d n J θ (tensorBasis d n U))
          2 (stdGaussianFin (2*d^n)) :=
  CertificationGaussian.Consumer.qudit_moment d n J θ (tensorBasis d n U) p hp

theorem qudit_tensor_polynomial_realization (d n : ℕ) (J : Finset ℕ) (θ : ℕ → ℝ)
    (U : Matrix (QIT.TensorPower (Fin d) n) (QIT.TensorPower (Fin d) n) ℂ) :
    ∃ P : MvPolynomial (Fin (2*d^n)) ℝ, P.totalDegree ≤ 4 ∧
      (∀ x, MvPolynomial.eval x P = CertificationGaussian.quditStandardQuartic d n J θ (tensorBasis d n U) x) ∧
      Measurable (CertificationGaussian.quditStandardQuartic d n J θ (tensorBasis d n U)) :=
  ⟨CertificationGaussian.quditPolynomial d n J θ (tensorBasis d n U),
    CertificationGaussian.degree_quditPolynomial d n J θ (tensorBasis d n U),
    CertificationGaussian.eval_quditPolynomial d n J θ (tensorBasis d n U),
    CertificationGaussian.quditStandardQuartic_measurable d n J θ (tensorBasis d n U)⟩

/-- The consumer is the paper's Gaussian quartic Q_U-v, with signed Hamming kernel. -/
theorem qudit_tensor_quartic_formula (d n : ℕ) (J : Finset ℕ) (θ : ℕ → ℝ)
    (U : Matrix (QIT.TensorPower (Fin d) n) (QIT.TensorPower (Fin d) n) ℂ)
    (x : Fin (2*d^n) → ℝ) :
    CertificationGaussian.quditStandardQuartic d n J θ (tensorBasis d n U) x =
      (1 / (d^n : ℝ)) *
        (∑ i, ∑ j,
          (CertificationGaussian.signedHammingKernel d n J θ * CertificationGaussian.signedHammingKernel d n J θ) i j *
          (‖(tensorBasis d n U).conjTranspose.mulVec
            (CertificationGaussian.complexCoordinate (CertificationGaussian.quditCoordinates d n x)) i‖^2-1) *
          (‖(tensorBasis d n U).conjTranspose.mulVec
            (CertificationGaussian.complexCoordinate (CertificationGaussian.quditCoordinates d n x)) j‖^2-1)) -
        CertificationGaussian.kernelVarianceScale d n J θ := by
  simpa only [CertificationGaussian.quditStandardQuartic, Function.comp_apply, CertificationGaussian.quditQuartic,
    CertificationGaussian.qudit_card, Nat.cast_pow] using
    CertificationGaussian.gaussianQuartic_formula (tensorBasis d n U) (CertificationGaussian.signedHammingKernel d n J θ)
      (CertificationGaussian.kernelVarianceScale d n J θ) (CertificationGaussian.quditCoordinates d n x)

end LocalCertification.Quantum
