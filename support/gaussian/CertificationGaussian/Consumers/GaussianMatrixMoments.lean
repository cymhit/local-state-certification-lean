import CertificationGaussian.GaussianMatrixOperatorMoments

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- The recursive and explicit upper bounds for even Gaussian trace moments use the same covariance operator norm. -/
theorem hermitian_matrix_moments {I N : Type*} [Fintype I] [DecidableEq I]
    [Fintype N] [DecidableEq N] (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) (p : Nat) :
    gaussianTraceMoment H (p+1) ≤ (2*p+1:Nat)*
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖*gaussianTraceMoment H p ∧
    gaussianTraceMoment H p ≤ (Fintype.card N:ℝ)*(Nat.doubleFactorial (2*p-1):ℝ)*
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖^p :=
  ⟨gaussianTraceMoment_recursion H hH p, gaussianTraceMoment_bound H hH p⟩

/-- Two genuinely noncommuting Hermitian coefficients. -/
def pauliGaussianCoefficients : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0,1;1,0], !![1,0;0,-1]]

theorem pauliGaussianCoefficients_hermitian (i : Fin 2) :
    (pauliGaussianCoefficients i).IsHermitian := by
  fin_cases i <;> change _ᴴ = _ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauliGaussianCoefficients, Matrix.conjTranspose_apply]

theorem pauliGaussianCoefficients_noncommuting :
    pauliGaussianCoefficients 0 * pauliGaussianCoefficients 1 ≠
      pauliGaussianCoefficients 1 * pauliGaussianCoefficients 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [pauliGaussianCoefficients, Matrix.mul_apply, Fin.sum_univ_two] at h01

theorem pauliGaussianCovariance :
    gaussianMatrixCovariance pauliGaussianCoefficients = (2:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [gaussianMatrixCovariance, pauliGaussianCoefficients, Fin.sum_univ_two,
      pow_two, Matrix.mul_apply]

/-- A concrete fourth operator-moment consumer with noncommuting matrices, not a scalarized series. -/
theorem pauliGaussian_fourth_operator_moment :
    ∫ x : Fin 2 → ℝ, ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
      (gaussianMatrixSeries pauliGaussianCoefficients x)‖^4 ∂realGaussianProduct (Fin 2) ≤ 24 := by
  have h := gaussianMatrixSeries_opNorm_moment_bound pauliGaussianCoefficients
    pauliGaussianCoefficients_hermitian (p := 2) (by decide)
  rw [pauliGaussianCovariance, map_smul, map_one, norm_smul] at h
  norm_num [Nat.doubleFactorial] at h
  exact h

/-- The first second moment and p=0 base case are covered without a special Gaussian assumption. -/
theorem first_trace_moment {I N : Type*} [Fintype I] [DecidableEq I]
    [Fintype N] [DecidableEq N] (H : I → Matrix N N ℂ) (hH : ∀ i, (H i).IsHermitian) :
    gaussianTraceMoment H 0 = (Fintype.card N:ℝ) ∧
    gaussianTraceMoment H 1 ≤ (Fintype.card N:ℝ)*
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖ := by
  refine ⟨gaussianTraceMoment_zero H, ?_⟩
  simpa [Nat.doubleFactorial] using gaussianTraceMoment_bound H hH 1

/-- Empty matrix dimension has zero trace moments, including the zeroth moment. -/
theorem empty_dimension_trace_moment (H : Fin 3 → Matrix (Fin 0) (Fin 0) ℂ) (p : Nat) :
    gaussianTraceMoment H p = 0 := by simp [gaussianTraceMoment, Matrix.trace]

/-- An empty Gaussian family gives the zero operator; positive moments vanish. -/
theorem empty_family_operator_moment (p : Nat) (hp : 0 < p) :
    ∫ x : Fin 0 → ℝ, ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
      (gaussianMatrixSeries (fun i : Fin 0 => Fin.elim0 i) x)‖^(2*p)
      ∂realGaussianProduct (Fin 0) = 0 := by
  simp [gaussianMatrixSeries, Nat.ne_zero_of_lt hp]

end CertificationGaussian.Consumers
