import CertificationGaussian.QuarticRadiusSphereTransfer
import CertificationGaussian.Consumers.UniformSphere

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal
namespace CertificationGaussian.Consumers
/-- Uniform processed-probability bound on the standard sphere for an arbitrary fixed signed kernel and every product measurement basis. -/
theorem uniform_standard_sphere_processed_probability_via_packing {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : Nat, ∀ n ≥ N,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        {ψ | ∃ U : Fin n → LocalUnitary d,
          (1+C/n)*kernelVarianceScale d n J θ <
            (d:ℝ)^n*‖processedProbability (tensorUnitaryMatrix d n U)
              (signedHammingKernel d n J θ) ψ‖^2} ≤
      ENNReal.ofReal (Real.exp (-c*(n:ℝ)^3)) := by
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  obtain ⟨N, hN⟩ := uniform_product_score_standard_sphere_via_packing hd J θ hθ
  refine ⟨Real.log d/16, 16, div_pos (Real.log_pos hdR) (by norm_num), by norm_num, N, ?_⟩
  intro n hn
  have he : {ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 |
      ∃ U : Fin n → LocalUnitary d, (1+16/n)*kernelVarianceScale d n J θ <
        (d:ℝ)^n*‖processedProbability (tensorUnitaryMatrix d n U) (signedHammingKernel d n J θ) ψ‖^2} =
      (allProductSphereGood d n J θ)ᶜ := by
    ext ψ
    simp only [allProductSphereGood, mem_compl_iff, mem_ofPred_eq, not_forall, not_le,
      quditSphereScore_sq_norm]
  rw [he]
  exact hN n hn


end CertificationGaussian.Consumers
