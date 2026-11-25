import CertificationGaussian.KernelOperator

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Finset
namespace CertificationGaussian

section Matrix
variable {I : Type*} [Fintype I]

/-- For a real symmetric matrix the trace of its square is the entry-square sum. -/
theorem trace_square_eq_sum_sq (R : Matrix I I ℝ) (hR : ∀ i j, R i j = R j i) :
    Matrix.trace (R * R) = ∑ i, ∑ j, (R i j)^2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hR j i, pow_two]

theorem square_matrix_symm (R : Matrix I I ℝ) (hR : ∀ i j, R i j = R j i)
    (i j : I) : (R * R) i j = (R * R) j i := by
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [hR i k, hR k j]
  ring

variable [DecidableEq I]

/-- Apply the actual Euclidean operator estimate to each matrix column. -/
theorem matrix_square_column_sum_le (R : Matrix I I ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R‖ ≤ L) (j : I) :
    ∑ i, ((R * R) i j)^2 ≤ L^2 * ∑ i, (R i j)^2 := by
  let z : EuclideanSpace ℝ I := WithLp.toLp 2 (fun i => R i j)
  let T := Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R
  have hn : ‖T z‖ ≤ L * ‖z‖ :=
    (T.le_opNorm z).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg z))
  have hs := (sq_le_sq₀ (norm_nonneg (T z)) (mul_nonneg hL (norm_nonneg z))).mpr hn
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

/-- Trace R^4 is controlled by the Euclidean operator bound times trace R^2. -/
theorem trace_four_le_norm_sq_trace_square (R : Matrix I I ℝ)
    (hR : ∀ i j, R i j = R j i) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R‖ ≤ L) :
    Matrix.trace (R^4) ≤ L^2 * Matrix.trace (R*R) := by
  have hpow : R^4 = (R*R)*(R*R) := by
    rw [show (4 : Nat) = 2+2 from rfl, pow_add, pow_two]
  rw [hpow, trace_square_eq_sum_sq (R*R) (square_matrix_symm R hR),
    trace_square_eq_sum_sq R hR]
  calc
    ∑ i, ∑ j, ((R*R) i j)^2 = ∑ j, ∑ i, ((R*R) i j)^2 := Finset.sum_comm
    _ ≤ ∑ j, L^2 * ∑ i, (R i j)^2 :=
      Finset.sum_le_sum (fun j _ => matrix_square_column_sum_le R hL hbound j)
    _ = L^2 * ∑ i, ∑ j, (R i j)^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

end Matrix

/-- The fourth-trace estimate for the signed kernel in the quartic variance bound. -/
theorem signedHammingKernel_trace_four_le {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) :
    Matrix.trace ((signedHammingKernel d n J θ)^4) ≤
      (kernelWeightL1 J θ)^2 * ((d^n : Nat) * kernelVarianceScale d n J θ) := by
  have h := trace_four_le_norm_sq_trace_square (signedHammingKernel d n J θ)
    (signedHammingKernel_symm d n J θ) (kernelWeightL1_nonneg J θ)
    (signedHammingKernel_operator_norm hd J hJ θ)
  rwa [signedHammingKernel_sq_trace hd J hJ θ] at h

end CertificationGaussian
