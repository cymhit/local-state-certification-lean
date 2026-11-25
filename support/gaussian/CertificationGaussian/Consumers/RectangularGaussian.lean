import CertificationGaussian.RectangularGaussianExpectation

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- One absolute positive constant simultaneously bounds every finite rectangular Gaussian family. -/
theorem rectangular_gaussian_universal_constant : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (m r c : Nat) (H : Fin m → Matrix (Fin r) (Fin c) ℂ),
    (∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries H x)‖ ∂realGaussianProduct (Fin m)) ≤
      C₀*Real.sqrt (Real.log (2*((r:ℝ)+c))) *
        max (Real.sqrt ‖Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (gaussianLeftCovariance H)‖)
          (Real.sqrt ‖Matrix.toEuclideanCLM (n := Fin c) (𝕜 := ℂ) (gaussianRightCovariance H)‖) := by
  refine ⟨gaussianMatrixExpectationConstant, gaussianMatrixExpectationConstant_pos, ?_⟩
  intro m r c H
  simpa only [Fintype.card_fin] using rectangularGaussian_expectation_bound H

/-- A genuine 2 by 5 family uses both covariance orientations and has all finite Lp norms. -/
theorem rectangular_two_by_five (H : Fin 3 → Matrix (Fin 2) (Fin 5) ℂ) :
    (∀ p : ℝ≥0∞, p ≠ ∞ → MemLp
      (fun x => ‖rectangularEuclideanCLM (gaussianMatrixSeries H x)‖) p
      (realGaussianProduct (Fin 3))) ∧
    (∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries H x)‖ ∂realGaussianProduct (Fin 3)) ≤
      gaussianMatrixExpectationConstant * Real.sqrt (Real.log 14) *
        max (Real.sqrt ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (gaussianLeftCovariance H)‖)
          (Real.sqrt ‖Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℂ) (gaussianRightCovariance H)‖) := by
  constructor
  · exact rectangularGaussian_opNorm_memLp H
  · simpa only [Fintype.card_fin, Nat.cast_ofNat, show (2:ℝ)*(2+5)=14 by norm_num] using
      rectangularGaussian_expectation_bound H

/-- A complex nonsquare row tests the conjugate-transpose direction of the dilation. -/
def complexGaussianRow : Matrix (Fin 1) (Fin 2) ℂ := !![1, Complex.I]

theorem complexGaussianRow_dilation :
    hermitianDilation complexGaussianRow (Sum.inl 0) (Sum.inr 1) = Complex.I ∧
    hermitianDilation complexGaussianRow (Sum.inr 1) (Sum.inl 0) = -Complex.I ∧
    ‖hermitianDilation complexGaussianRow‖ = ‖rectangularEuclideanCLM complexGaussianRow‖ := by
  refine ⟨by simp [hermitianDilation, complexGaussianRow],
    by simp [hermitianDilation, complexGaussianRow, Matrix.conjTranspose_apply], ?_⟩
  rw [hermitianDilation_norm, rectangularEuclideanCLM_norm]

theorem complexGaussianRow_covariances :
    gaussianLeftCovariance (fun _ : Fin 1 => complexGaussianRow) = !![2] ∧
    gaussianRightCovariance (fun _ : Fin 1 => complexGaussianRow) = !![1,Complex.I; -Complex.I,1] := by
  constructor
  · ext a b
    fin_cases a
    fin_cases b
    norm_num [gaussianLeftCovariance, complexGaussianRow, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [gaussianRightCovariance, complexGaussianRow, Matrix.mul_apply]

/-- The rectangular theorem retains the correct zero behavior for either empty dimension. -/
theorem empty_rectangular_expectations (m c r : Nat)
    (H : Fin m → Matrix (Fin 0) (Fin c) ℂ) (K : Fin m → Matrix (Fin r) (Fin 0) ℂ) :
    (∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries H x)‖ ∂realGaussianProduct (Fin m)) = 0 ∧
    (∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries K x)‖ ∂realGaussianProduct (Fin m)) = 0 := by
  have hH (x : Fin m → ℝ) : rectangularEuclideanCLM (gaussianMatrixSeries H x) = 0 :=
    Subsingleton.elim _ _
  have hK (x : Fin m → ℝ) : rectangularEuclideanCLM (gaussianMatrixSeries K x) = 0 :=
    Subsingleton.elim _ _
  simp [hH, hK]

end CertificationGaussian.Consumers
