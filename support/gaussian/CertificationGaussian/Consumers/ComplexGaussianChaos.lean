import CertificationGaussian.ComplexGaussianDecoupling

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- The actual centered CN bound has one constant outside every dimension and coefficient tensor. -/
theorem centered_complex_gaussian_universal_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (m r c : Nat) (A : Fin m → Fin m → Matrix (Fin r) (Fin c) ℂ),
    (∫ x, ‖complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i)‖
      ∂pairedGaussian (Fin m)) ≤ C *
      Real.sqrt (Real.log (2*((r:ℝ)+c)) * Real.log (2*(m:ℝ)*((r:ℝ)+c))) *
      gaussianChaosFlatteningNorm A := by
  refine ⟨4*gaussianMatrixChaosConstant,
    mul_pos (by norm_num) gaussianMatrixChaosConstant_pos, ?_⟩
  intro m r c A
  simpa only [Fintype.card_fin] using complexGaussianQuadratic_expectation_bound A

/-- Equal-dimension single-log form for all coefficients, including D=0. -/
theorem centered_complex_equal_dimension_universal_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (D : Nat) (A : Fin D → Fin D → Matrix (Fin D) (Fin D) ℂ),
    (∫ x, ‖complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i)‖
      ∂pairedGaussian (Fin D)) ≤ C * Real.log (2*(D:ℝ)) * gaussianChaosFlatteningNorm A := by
  refine ⟨8*gaussianMatrixChaosConstant,
    mul_pos (by norm_num) gaussianMatrixChaosConstant_pos, ?_⟩
  intro D A
  simpa only [Fintype.card_fin] using complexGaussianQuadratic_equal_dimension_bound A

def nilpotentChaosMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]

theorem nilpotentChaosMatrix_not_hermitian : ¬nilpotentChaosMatrix.IsHermitian := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h.eq
  norm_num [nilpotentChaosMatrix, Matrix.conjTranspose_apply] at he

/-- A non-Hermitian coefficient has its genuine matrix mean and centered expectation bound. -/
theorem nilpotent_complex_gaussian_mean_and_bound :
    (∫ x, complexGaussianQuadratic (fun _ _ : Fin 1 => nilpotentChaosMatrix) x
      ∂pairedGaussian (Fin 1)) = rectangularEuclideanCLM nilpotentChaosMatrix ∧
    (∫ x, ‖complexGaussianQuadratic (fun _ _ : Fin 1 => nilpotentChaosMatrix) x -
      rectangularEuclideanCLM nilpotentChaosMatrix‖ ∂pairedGaussian (Fin 1)) ≤
      (4*gaussianMatrixChaosConstant) * Real.sqrt (Real.log 8 * Real.log 8) *
        gaussianChaosFlatteningNorm (fun _ _ : Fin 1 => nilpotentChaosMatrix) := by
  constructor
  · simpa using complexGaussianQuadratic_integral (fun _ _ : Fin 1 => nilpotentChaosMatrix)
  · convert complexGaussianQuadratic_expectation_bound (fun _ _ : Fin 1 => nilpotentChaosMatrix) using 1 <;>
      norm_num

/-- A true nonsquare 2 by 5 complex coefficient array keeps its actual diagonal mean. -/
theorem centered_complex_two_by_five (A : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 5) ℂ) :
    (∫ x, complexGaussianQuadratic A x ∂pairedGaussian (Fin 3)) =
      rectangularEuclideanCLM (∑ i, A i i) ∧
    (∫ x, ‖complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i)‖
      ∂pairedGaussian (Fin 3)) ≤ (4*gaussianMatrixChaosConstant) *
      Real.sqrt (Real.log 14 * Real.log 42) * gaussianChaosFlatteningNorm A := by
  refine ⟨complexGaussianQuadratic_integral A, ?_⟩
  convert complexGaussianQuadratic_expectation_bound A using 1
  norm_num

theorem empty_complex_gaussian_center (r c : Nat)
    (A : Fin 0 → Fin 0 → Matrix (Fin r) (Fin c) ℂ) :
    (∫ x, ‖complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i)‖
      ∂pairedGaussian (Fin 0)) = 0 := by
  simp [complexGaussianQuadratic, matrixSesquilinear, rectangularEuclideanCLM]

theorem complex_gaussian_empty_dimensions (m r c : Nat)
    (A : Fin m → Fin m → Matrix (Fin 0) (Fin c) ℂ)
    (B : Fin m → Fin m → Matrix (Fin r) (Fin 0) ℂ) :
    (∫ x, ‖complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i)‖
      ∂pairedGaussian (Fin m)) = 0 ∧
    (∫ x, ‖complexGaussianQuadratic B x-rectangularEuclideanCLM (∑ i, B i i)‖
      ∂pairedGaussian (Fin m)) = 0 := by
  have hA (x : Fin 2 × Fin m → ℝ) :
      complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i) = 0 := Subsingleton.elim _ _
  have hB (x : Fin 2 × Fin m → ℝ) :
      complexGaussianQuadratic B x-rectangularEuclideanCLM (∑ i, B i i) = 0 := Subsingleton.elim _ _
  simp [hA, hB]

end CertificationGaussian.Consumers
