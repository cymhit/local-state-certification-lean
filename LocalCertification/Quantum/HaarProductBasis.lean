import CertificationGaussian.Consumers.HaarSpherePacking
import LocalCertification.Quantum.UniformProductBasis
import CertificationGaussian.Consumers.HaarSphere

open scoped BigOperators Topology ENNReal
open MeasureTheory Metric Set
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

/-- Actual full-unitary Haar orbit, identified with normalized sphere area for any initial unit vector. -/
theorem qudit_haar_orbit_eq_sphere (d n : ℕ) (hd : 2 ≤ d)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :
    (CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)).map
      (fun W => CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ) =
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) := by
  let : Nonempty (CertificationGaussian.QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  exact CertificationGaussian.complexUnitaryHaar_orbit_map _ ψ

/-- Main-engine Haar theorem: the actual QIT product basis and Born probabilities,
with the threshold uniform over all initial unit vectors and all continuous product bases. -/
theorem qudit_haar_product_basis_score_bound (d : ℕ) (hd : 2 ≤ d) (J : Finset ℕ)
    (θ : ℕ → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
        {W | ∃ U : Fin n → CertificationGaussian.LocalUnitary d,
          (1 + C / n) * CertificationGaussian.kernelVarianceScale d n J θ <
            (d : ℝ) ^ n * ‖CertificationGaussian.processedProbability
              (tensorBasis d n (qitProductBasis d n U)) (CertificationGaussian.signedHammingKernel d n J θ)
              (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ)‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 3)) := by
  simpa only [tensorBasis_qitProductBasis] using
    CertificationGaussian.Consumers.uniform_haar_orbit_processed_probability_via_packing hd J θ hθ

end LocalCertification.Quantum
