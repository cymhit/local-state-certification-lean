import CertificationGaussian.GaussianChaosExpectation

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- A single absolute positive constant precedes all dimensions and every complex coefficient tensor. -/
theorem gaussian_chaos_universal_constant : ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (m r c : Nat) (A : Fin m → Fin m → Matrix (Fin r) (Fin c) ℂ),
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
      ∂(realGaussianProduct (Fin m)).prod (realGaussianProduct (Fin m))) ≤
      C₁ * Real.sqrt (Real.log (2*((r:ℝ)+c)) * Real.log (2*(m:ℝ)*((r:ℝ)+c))) *
        gaussianChaosFlatteningNorm A := by
  refine ⟨gaussianMatrixChaosConstant, gaussianMatrixChaosConstant_pos, ?_⟩
  intro m r c A
  simpa only [Fintype.card_fin] using gaussianMatrixChaos_expectation_bound A

/-- An arbitrary complex 3 by 3 coefficient array of 2 by 5 matrices tests both logarithmic factors. -/
theorem gaussian_chaos_two_by_five (A : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 5) ℂ) :
    Integrable (fun z => ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖)
      ((realGaussianProduct (Fin 3)).prod (realGaussianProduct (Fin 3))) ∧
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
      ∂(realGaussianProduct (Fin 3)).prod (realGaussianProduct (Fin 3))) ≤
      gaussianMatrixChaosConstant * Real.sqrt (Real.log 14 * Real.log 42) *
        gaussianChaosFlatteningNorm A := by
  refine ⟨gaussianMatrixChaos_opNorm_integrable A, ?_⟩
  convert gaussianMatrixChaos_expectation_bound A using 1
  norm_num

/-- This complex off-diagonal tensor distinguishes the two mixed matricizations. -/
def offDiagonalChaosTensor (i j : Fin 2) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => if i=0 ∧ j=1 then Complex.I else 0

theorem offDiagonalChaos_flattenings :
    chaosFlattening₃ offDiagonalChaosTensor (0,0) (1,0) = Complex.I ∧
    chaosFlattening₄ offDiagonalChaosTensor (0,0) (1,0) = 0 ∧
    chaosFlattening₃ offDiagonalChaosTensor ≠ chaosFlattening₄ offDiagonalChaosTensor := by
  refine ⟨by simp [chaosFlattening₃, offDiagonalChaosTensor],
    by simp [chaosFlattening₄, offDiagonalChaosTensor], ?_⟩
  intro h
  have he := congrArg (fun M : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ => M (0,0) (1,0)) h
  simp [chaosFlattening₃, chaosFlattening₄, offDiagonalChaosTensor] at he

theorem offDiagonalChaos_actual_series (x y : Fin 2 → ℝ) :
    gaussianMatrixChaos offDiagonalChaosTensor x y 0 0 =
      (x 0:ℂ)*(y 1:ℂ)*Complex.I := by
  simp [gaussianMatrixChaos, offDiagonalChaosTensor, Matrix.sum_apply, Fin.sum_univ_two]

/-- The actual product expectation is zero for an empty Gaussian family. -/
theorem empty_gaussian_chaos (r c : Nat)
    (A : Fin 0 → Fin 0 → Matrix (Fin r) (Fin c) ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
      ∂(realGaussianProduct (Fin 0)).prod (realGaussianProduct (Fin 0))) = 0 := by
  simp [gaussianMatrixChaos, rectangularEuclideanCLM]

theorem empty_rectangular_chaos (m r c : Nat)
    (A : Fin m → Fin m → Matrix (Fin 0) (Fin c) ℂ)
    (B : Fin m → Fin m → Matrix (Fin r) (Fin 0) ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
      ∂(realGaussianProduct (Fin m)).prod (realGaussianProduct (Fin m))) = 0 ∧
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos B z.1 z.2)‖
      ∂(realGaussianProduct (Fin m)).prod (realGaussianProduct (Fin m))) = 0 := by
  have hA (x y : Fin m → ℝ) : rectangularEuclideanCLM (gaussianMatrixChaos A x y) = 0 :=
    Subsingleton.elim _ _
  have hB (x y : Fin m → ℝ) : rectangularEuclideanCLM (gaussianMatrixChaos B x y) = 0 :=
    Subsingleton.elim _ _
  simp [hA, hB]

end CertificationGaussian.Consumers
