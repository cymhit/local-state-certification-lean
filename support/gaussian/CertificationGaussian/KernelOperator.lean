import CertificationGaussian.HammingKernel
import Mathlib.Analysis.Convex.Birkhoff

/- Operator bounds use the Euclidean L2 matrix norm, not the raw Pi sup norm.
Only individual shell kernels are doubly stochastic; signed sums stay signed. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Finset
namespace CertificationGaussian

def kernelWeightL1 (J : Finset Nat) (θ : Nat → ℝ) : ℝ := ∑ k ∈ J, |θ k|

theorem kernelWeightL1_nonneg (J : Finset Nat) (θ : Nat → ℝ) :
    0 ≤ kernelWeightL1 J θ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem distanceAverage_doublyStochastic {d n k : Nat} (hd : 2 ≤ d) (hk : k ≤ n) :
    distanceAverage d n k ∈ doublyStochastic ℝ (QuditIndex d n) :=
  mem_doublyStochastic_iff_sum.mpr
    ⟨distanceAverage_nonneg d n k, distanceAverage_row_sum hd hk, distanceAverage_column_sum hd hk⟩

theorem distanceAverage_l2_norm_le_one {d n k : Nat} (hd : 2 ≤ d) (hk : k ≤ n) :
    ‖distanceAverage d n k‖ ≤ 1 :=
  Matrix.l2_opNorm_le_one_of_mem_doublyStochastic (distanceAverage_doublyStochastic hd hk)

/-- The operator-norm bound for the Hamming kernel with real signed coefficients. -/
theorem signedHammingKernel_l2_norm {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) :
    ‖signedHammingKernel d n J θ‖ ≤ kernelWeightL1 J θ := by
  unfold signedHammingKernel kernelWeightL1
  refine (norm_sum_le J _).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_smul, Real.norm_eq_abs]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (distanceAverage_l2_norm_le_one hd (hJ k hk)) (abs_nonneg (θ k))

/-- Explicit continuous operator norm interface on EuclideanSpace. -/
theorem signedHammingKernel_operator_norm {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) :
    ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℝ) (signedHammingKernel d n J θ)‖ ≤ kernelWeightL1 J θ := by
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact signedHammingKernel_l2_norm hd J hJ θ

theorem signedHammingKernel_norm_apply {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (z : EuclideanSpace ℝ (QuditIndex d n)) :
    ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℝ) (signedHammingKernel d n J θ) z‖ ≤ kernelWeightL1 J θ * ‖z‖ :=
  ((Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℝ) (signedHammingKernel d n J θ)).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (signedHammingKernel_operator_norm hd J hJ θ) (norm_nonneg z))

theorem signedHammingKernel_row_abs {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (x : QuditIndex d n) :
    ∑ y, |signedHammingKernel d n J θ x y| ≤ kernelWeightL1 J θ := by
  classical
  calc
    ∑ y, |signedHammingKernel d n J θ x y| ≤
        ∑ y, ∑ k ∈ J, |θ k| * distanceAverage d n k x y := by
      apply Finset.sum_le_sum
      intro y _
      rw [signedHammingKernel_apply]
      calc
        _ ≤ ∑ k ∈ J, |θ k * distanceAverage d n k x y| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul, abs_of_nonneg (distanceAverage_nonneg d n k x y)]
    _ = kernelWeightL1 J θ := by
      unfold kernelWeightL1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.mul_sum, distanceAverage_row_sum hd (hJ k hk), mul_one]

theorem kernelVarianceScale_le_weight_sq {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) :
    kernelVarianceScale d n J θ ≤ (kernelWeightL1 J θ)^2 := by
  classical
  let x : QuditIndex d n := fun _ => ⟨0, by omega⟩
  rw [← signedHammingKernel_row_sq hd J hJ θ x]
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (QuditIndex d n)))
    (f := fun y => |signedHammingKernel d n J θ x y|) (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at hs
  exact hs.trans ((sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (kernelWeightL1_nonneg J θ)).mpr (signedHammingKernel_row_abs hd J hJ θ x))

/-- sum θ = 1 guarantees a nonzero coefficient, while zero coefficients remain allowed. -/
theorem kernelVarianceScale_pos {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    0 < kernelVarianceScale d n J θ := by
  classical
  have hex : ∃ k ∈ J, θ k ≠ 0 := by
    by_contra! h
    have hz : ∑ k ∈ J, θ k = 0 := Finset.sum_eq_zero h
    rw [hz] at hθ
    norm_num at hθ
  obtain ⟨k, hk, hk0⟩ := hex
  apply lt_of_lt_of_le (div_pos (sq_pos_of_ne_zero hk0) (distance_denominator_pos hd (hJ k hk)))
  unfold kernelVarianceScale
  exact Finset.single_le_sum
    (f := fun l => (θ l)^2 / ((Nat.choose n l : ℝ) * ((d-1 : Nat) : ℝ)^l))
    (fun l _ => by positivity) hk

end CertificationGaussian
