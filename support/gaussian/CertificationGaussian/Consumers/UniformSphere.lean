import CertificationGaussian.SphereTransfer

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal
namespace CertificationGaussian.Consumers

/-- The score is exactly the requested dimension-scaled Euclidean processed-probability deviation. -/
theorem quditSphereScore_sq_norm (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    (quditSphereScore d n J θ U ψ)^2 =
      (d:ℝ)^n*‖processedProbability U (signedHammingKernel d n J θ) ψ‖^2 := by
  rw [quditSphereScore, sphereScore, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), qudit_card, Nat.cast_pow]

/-- Its actual coordinates are R*p_U minus the uniform probability vector. -/
theorem processedProbability_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (R : Matrix I I ℝ) (ψ : EuclideanSpace ℂ I) (i : I) :
    processedProbability U R ψ i =
      (∑ j, R i j * Complex.normSq (U.conjTranspose.mulVec (WithLp.ofLp ψ) j))-(Fintype.card I:ℝ)⁻¹ := by
  change R.mulVec (basisProbability U ψ) i-(Fintype.card I:ℝ)⁻¹ = _
  simp only [Matrix.mulVec, dotProduct, basisProbability_apply]

/-- Uniform processed-probability bound on the standard sphere for an arbitrary fixed signed kernel and every product measurement basis. -/
theorem uniform_standard_sphere_processed_probability {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : Nat, ∀ n ≥ N,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        {ψ | ∃ U : Fin n → LocalUnitary d,
          (1+C/n)*kernelVarianceScale d n J θ <
            (d:ℝ)^n*‖processedProbability (tensorUnitaryMatrix d n U)
              (signedHammingKernel d n J θ) ψ‖^2} ≤
      ENNReal.ofReal (Real.exp (-c*(n:ℝ)^3)) := by
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  obtain ⟨N, hN⟩ := uniform_product_score_standard_sphere hd J θ hθ
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
