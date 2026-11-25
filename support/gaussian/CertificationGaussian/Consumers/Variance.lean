import CertificationGaussian.GaussianTail

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CertificationGaussian.Consumers

/-- Actual general qudit consumer: signed kernel, arbitrary unitary, and arbitrary real p>=2. -/
theorem general_mean_variance_moment {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) (p : ℝ) (hp : 2 ≤ p) :
    (∫ x, quditQuartic d n J θ U x ∂pairedGaussian (QuditIndex d n)) = 0 ∧
    (∫ x, gaussianQuartic U (signedHammingKernel d n J θ) 0 x
      ∂pairedGaussian (QuditIndex d n)) = kernelVarianceScale d n J θ ∧
    variance (gaussianQuartic U (signedHammingKernel d n J θ) 0)
      (pairedGaussian (QuditIndex d n)) =
      (2 * Matrix.trace ((signedHammingKernel d n J θ)^4) +
        6 * (d^n : ℝ) * (kernelVarianceScale d n J θ)^2) / (d^n : ℝ)^2 ∧
    (∫ x, (quditQuartic d n J θ U x)^2 ∂pairedGaussian (QuditIndex d n)) ≤
      8 * (kernelWeightL1 J θ)^2 * kernelVarianceScale d n J θ / (d^n : ℝ) ∧
    MemLp (quditQuartic d n J θ U) (ENNReal.ofReal p) (pairedGaussian (QuditIndex d n)) ∧
    eLpNorm (quditQuartic d n J θ U) (ENNReal.ofReal p) (pairedGaussian (QuditIndex d n)) ≤
      ENNReal.ofReal (5*(p-1)^2) * eLpNorm (quditQuartic d n J θ U) 2
        (pairedGaussian (QuditIndex d n)) := by
  exact ⟨quditQuartic_mean_zero hd J hJ θ U hU, quditEnergy_mean hd J hJ θ U hU,
    quditEnergy_variance hd J hJ θ U hU, quditQuartic_second_moment_le hd J hJ θ U hU,
    gaussianQuartic_memLp U _ _ p hp, quditQuartic_eLpNorm d n J θ U p hp⟩

/-- A genuinely signed example: theta_1=2, theta_2=-1, sum theta=1. -/
theorem signed_example_mean :
    ∫ x, gaussianQuartic (1 : Matrix (QuditIndex 2 2) (QuditIndex 2 2) ℂ)
      (signedHammingKernel 2 2 {1,2} (fun k => if k=1 then 2 else -1)) 0 x
      ∂pairedGaussian (QuditIndex 2 2) = 3 := by
  have h := quditEnergy_mean (d := 2) (n := 2) (by decide) {1,2}
    (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk; rcases hk with rfl | rfl <;> omega)
    (fun k => if k=1 then 2 else -1) 1 (by simp)
  norm_num [kernelVarianceScale, Nat.choose] at h ⊢
  exact h

theorem signed_example_second_bound :
    ∫ x, (quditQuartic 2 2 {1,2} (fun k => if k=1 then 2 else -1)
      (1 : Matrix (QuditIndex 2 2) (QuditIndex 2 2) ℂ) x)^2
      ∂pairedGaussian (QuditIndex 2 2) ≤ 54 := by
  have h := quditQuartic_second_moment_le (d := 2) (n := 2) (by decide) {1,2}
    (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk; rcases hk with rfl | rfl <;> omega)
    (fun k => if k=1 then 2 else -1) 1 (by simp)
  norm_num [kernelWeightL1, kernelVarianceScale, Nat.choose] at h ⊢
  exact h

/-- Empty finite coordinate sets remain covered by the general centered matrix statement. -/
theorem empty_matrix_centered_second (U : Matrix (Fin 0) (Fin 0) ℂ)
    (hU : U ∈ unitary (Matrix (Fin 0) (Fin 0) ℂ)) (R : Matrix (Fin 0) (Fin 0) ℝ) :
    ∫ x, (gaussianQuartic U R 0 x)^2 ∂pairedGaussian (Fin 0) = 0 := by
  simpa [Matrix.trace, Matrix.diag] using gaussianQuartic_centered_second U hU R
    (fun i => Fin.elim0 i)

/-- The concrete p=n², relative v_n/n deviation used by the fixed-basis step. -/
theorem fixed_basis_n_squared_relative_tail {d n : Nat} (hd : 2 ≤ d) (hn : 2 ≤ n)
    (J : Finset Nat) (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) :
    (pairedGaussian (QuditIndex d n))
      {x | kernelVarianceScale d n J θ / (n:ℝ) ≤ |quditQuartic d n J θ U x|} ≤
      ENNReal.ofReal ((5*((n:ℝ)^2-1)^2 * Real.sqrt
        (8 * (kernelWeightL1 J θ)^2 * kernelVarianceScale d n J θ / (d^n : ℝ)) /
        (kernelVarianceScale d n J θ / (n:ℝ))) ^ ((n:ℝ)^2)) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  exact quditQuartic_abs_tail hd J hJ θ U hU ((n:ℝ)^2) (by nlinarith) _
    (div_pos (kernelVarianceScale_pos hd J hJ θ hθ) (by linarith))

end CertificationGaussian.Consumers
