import CertificationGaussian.KernelOperator

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumer

/-- A genuinely signed kernel; normalization of coefficients does not impose positivity. -/
theorem signed_kernel_identities {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    (∀ x, ∑ y, signedHammingKernel d n J θ x y = 1) ∧
    (∀ x, (signedHammingKernel d n J θ * signedHammingKernel d n J θ) x x =
      kernelVarianceScale d n J θ) ∧
    ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℝ) (signedHammingKernel d n J θ)‖ ≤
      kernelWeightL1 J θ ∧
    0 < kernelVarianceScale d n J θ ∧
    kernelVarianceScale d n J θ ≤ (kernelWeightL1 J θ)^2 := by
  refine ⟨?_, signedHammingKernel_sq_diag hd J hJ θ,
    signedHammingKernel_operator_norm hd J hJ θ, kernelVarianceScale_pos hd J hJ θ hθ,
    kernelVarianceScale_le_weight_sq hd J hJ θ⟩
  intro x
  rw [signedHammingKernel_row_sum hd J hJ θ, hθ]

theorem zero_dimension_sphere (d : Nat) (x : QuditIndex d 0) :
    (Finset.univ.filter (fun y : QuditIndex d 0 => hammingDistance x y = 0)).card = 1 := by
  simpa using hamming_sphere_card x 0

theorem shell_beyond_dimension {d n k : Nat} (x : QuditIndex d n) (hk : n < k) :
    (Finset.univ.filter (fun y : QuditIndex d n => hammingDistance x y = k)).card = 0 := by
  rw [hamming_sphere_card, Nat.choose_eq_zero_of_lt hk, zero_mul]

/-- Zero coefficients are admitted: the effective support can be smaller than J. -/
theorem zero_coefficient_variance_positive :
    0 < kernelVarianceScale 3 2 {1,2} (fun k => if k = 1 then 0 else 1) := by
  apply kernelVarianceScale_pos (by omega)
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  · norm_num

end CertificationGaussian.Consumer
