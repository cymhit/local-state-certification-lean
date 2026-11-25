import CertificationGaussian.HaarOrbit
import CertificationGaussian.Consumers.UniformSpherePacking

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal
namespace CertificationGaussian.Consumers
/-- The uniform product-basis score bound under the full-unitary Haar orbit of any fixed initial unit vector. -/
theorem uniform_product_score_haar_orbit_via_packing {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ N : Nat, ∀ n ≥ N, ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      complexUnitaryHaar (QuditIndex d n)
        {W | complexUnitarySphereAction (QuditIndex d n) W ψ ∉ allProductSphereGood d n J θ} ≤
      ENNReal.ofReal (Real.exp (-(Real.log d/16)*(n:ℝ)^3)) := by
  classical
  obtain ⟨N, hN⟩ := uniform_product_score_standard_sphere_via_packing hd J θ hθ
  refine ⟨N, fun n hn ψ => ?_⟩
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  have he := congrArg
    (fun μ : Measure (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) =>
      μ (allProductSphereGood d n J θ)ᶜ)
    (complexUnitaryHaar_orbit_map (QuditIndex d n) ψ)
  rw [Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right
    (allProductSphereGood_isClosed d n J θ).measurableSet.compl] at he
  have h := hN n hn
  rw [← he] at h
  exact h

/-- Uniform processed-probability event for a real signed Hamming kernel, Born probabilities,
all product measurement bases, and a state sampled from full complex-unitary Haar measure. -/
theorem uniform_haar_orbit_processed_probability_via_packing {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : Nat, ∀ n ≥ N,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      complexUnitaryHaar (QuditIndex d n)
        {W | ∃ U : Fin n → LocalUnitary d,
          (1+C/n)*kernelVarianceScale d n J θ <
            (d:ℝ)^n*‖processedProbability (tensorUnitaryMatrix d n U)
              (signedHammingKernel d n J θ)
              (complexUnitarySphereAction (QuditIndex d n) W ψ)‖^2} ≤
      ENNReal.ofReal (Real.exp (-c*(n:ℝ)^3)) := by
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  obtain ⟨N, hN⟩ := uniform_product_score_haar_orbit_via_packing hd J θ hθ
  refine ⟨Real.log d/16, 16, div_pos (Real.log_pos hdR) (by norm_num), by norm_num, N, ?_⟩
  intro n hn ψ
  simpa only [allProductSphereGood, mem_ofPred_eq, not_forall, not_le,
    quditSphereScore_sq_norm] using hN n hn ψ


end CertificationGaussian.Consumers
