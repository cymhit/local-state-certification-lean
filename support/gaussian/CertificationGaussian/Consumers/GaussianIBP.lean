import CertificationGaussian.GaussianMatrixPolynomial

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CertificationGaussian.Consumers

/-- A degree-seventeen polynomial belongs to every finite Lp, beyond the quartic moment layer. -/
theorem degree_seventeen_all_moments (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : Fin 2 → ℝ => x 0^17 + x 1^8) p (realGaussianProduct (Fin 2)) := by
  convert realGaussianProduct_polynomial_memLp
    ((MvPolynomial.X (0 : Fin 2))^17+(MvPolynomial.X 1)^8) p hp using 1
  funext x
  simp

/-- An imaginary-coefficient, mixed degree-nine polynomial satisfies actual Gaussian IBP. -/
theorem imaginary_mixed_ninth_ibp :
    ∫ x : Fin 2 → ℝ, (x 0 : ℂ)*(Complex.I*(x 0 : ℂ)^7*(x 1 : ℂ)^2)
      ∂realGaussianProduct (Fin 2) =
    ∫ x : Fin 2 → ℝ, 7*Complex.I*(x 0 : ℂ)^6*(x 1 : ℂ)^2
      ∂realGaussianProduct (Fin 2) := by
  have h := realGaussianProduct_complex_polynomial_ibp
    (MvPolynomial.C Complex.I*(MvPolynomial.X (0 : Fin 2))^7*(MvPolynomial.X 1)^2) 0
  norm_num [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, Pi.single_apply] at h
  convert h using 1; congr 1; funext x; ring

/-- Truly rectangular coefficients; no square-matrix or self-adjoint hypothesis enters L1. -/
theorem rectangular_entry_all_moments (H : Fin 3 → Matrix (Fin 2) (Fin 5) ℂ)
    (a : Fin 2) (b : Fin 5) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => gaussianMatrixSeries H x a b) p (realGaussianProduct (Fin 3)) :=
  gaussianMatrixSeries_entry_memLp H a b p hp

/-- The actual trace function, analytic partial derivative, and integrability are available together. -/
theorem matrix_trace_ibp_all_orders {I N : Type*} [Fintype I] [DecidableEq I]
    [Fintype N] [DecidableEq N] (H : I → Matrix N N ℂ) (A : Matrix N N ℂ)
    (k : Nat) (i : I) :
    Integrable (fun x => Matrix.trace (A*(gaussianMatrixSeries H x)^k)) (realGaussianProduct I) ∧
    Integrable (fun x : I → ℝ => deriv (fun t : ℝ =>
      Matrix.trace (A*(gaussianMatrixSeries H (Function.update x i t))^k)) (x i))
      (realGaussianProduct I) ∧
    (∫ x, (x i : ℂ)*Matrix.trace (A*(gaussianMatrixSeries H x)^k) ∂realGaussianProduct I) =
      ∫ x : I → ℝ, deriv (fun t : ℝ =>
        Matrix.trace (A*(gaussianMatrixSeries H (Function.update x i t))^k)) (x i)
        ∂realGaussianProduct I :=
  ⟨(gaussianMatrixSeries_trace_memLp H A k 1 (by simp)).integrable (by rfl),
    gaussianMatrixSeries_trace_deriv_integrable H A k i, gaussianMatrixSeries_trace_ibp H A k i⟩

/-- Constants in zero coordinates and exponent zero are both included. -/
theorem empty_coordinates_and_zero_exponent (P : MvPolynomial (Fin 0) ℂ) :
    MemLp (fun x : Fin 0 → ℝ => MvPolynomial.eval (fun j => (x j : ℂ)) P)
      0 (realGaussianProduct (Fin 0)) :=
  realGaussianProduct_complex_polynomial_memLp P 0 (by simp)

/-- Empty matrices have zero trace at every power, including the zeroth power. -/
theorem empty_matrix_trace (H : Fin 2 → Matrix (Fin 0) (Fin 0) ℂ) (x : Fin 2 → ℝ) (k : Nat) :
    Matrix.trace ((gaussianMatrixSeries H x)^k) = 0 := by simp [Matrix.trace]

end CertificationGaussian.Consumers
