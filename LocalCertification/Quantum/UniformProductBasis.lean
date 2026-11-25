import CertificationGaussian.Consumers.HaarSpherePacking
import LocalCertification.Quantum.GaussianMoments
import CertificationGaussian.Consumers.UniformSphere

open scoped BigOperators Topology ENNReal
open MeasureTheory Metric Set

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace LocalCertification.Quantum

/-- The actual product of local unitaries, expressed on QIT's recursive tensor labels. -/
def qitProductBasis (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d) :
    Matrix (QIT.TensorPower (Fin d) n) (QIT.TensorPower (Fin d) n) ℂ :=
  Matrix.reindex (quditTensorEquiv d n).symm (quditTensorEquiv d n).symm
    (CertificationGaussian.tensorUnitaryMatrix d n U)

theorem qitProductBasis_apply (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (i j : QIT.TensorPower (Fin d) n) :
    qitProductBasis d n U i j = ∏ k, (U k).1 (quditTensorEquiv d n i k) (quditTensorEquiv d n j k) := rfl

/-- Reindexing returns exactly the adapter's unique actual product-basis matrix. -/
theorem tensorBasis_qitProductBasis (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d) :
    tensorBasis d n (qitProductBasis d n U) = CertificationGaussian.tensorUnitaryMatrix d n U := by
  ext i j
  simp [tensorBasis, qitProductBasis, Matrix.reindex_apply]

/-- The coordinates are the actual signed-Hamming processing of Born probabilities, minus uniform. -/
theorem qitProductBasis_processed_coordinate (d n : ℕ) (J : Finset ℕ) (θ : ℕ → ℝ)
    (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ψ : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) (i : CertificationGaussian.QuditIndex d n) :
    CertificationGaussian.processedProbability (tensorBasis d n (qitProductBasis d n U))
      (CertificationGaussian.signedHammingKernel d n J θ) ψ i =
      (∑ j, CertificationGaussian.signedHammingKernel d n J θ i j *
        Complex.normSq ((tensorBasis d n (qitProductBasis d n U)).conjTranspose.mulVec (WithLp.ofLp ψ) j)) -
          ((d : ℝ) ^ n)⁻¹ := by
  simpa only [CertificationGaussian.qudit_card, Nat.cast_pow] using
    CertificationGaussian.Consumers.processedProbability_coordinate
      (tensorBasis d n (qitProductBasis d n U)) (CertificationGaussian.signedHammingKernel d n J θ) ψ i

/-- The full canonical-sphere theorem for all continuous product-unitary bases at once.
The only model premises are fixed d>=2 and the signed kernel's total mass one. -/
theorem qudit_uniform_product_basis_score_bound (d : ℕ) (hd : 2 ≤ d) (J : Finset ℕ)
    (θ : ℕ → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))
        {ψ | ∃ U : Fin n → CertificationGaussian.LocalUnitary d,
          (1 + C / n) * CertificationGaussian.kernelVarianceScale d n J θ <
            (d : ℝ) ^ n * ‖CertificationGaussian.processedProbability
              (tensorBasis d n (qitProductBasis d n U)) (CertificationGaussian.signedHammingKernel d n J θ) ψ‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 3)) := by
  simpa only [tensorBasis_qitProductBasis] using
    CertificationGaussian.Consumers.uniform_standard_sphere_processed_probability_via_packing hd J θ hθ

end LocalCertification.Quantum
