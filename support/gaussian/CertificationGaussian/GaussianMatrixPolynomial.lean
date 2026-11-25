import CertificationGaussian.GaussianPolynomialIBP
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CertificationGaussian

variable {I R C N : Type*} [Fintype I]

/-- Evaluation of a matrix of ordinary complex polynomials on real Gaussian coordinates. -/
def matrixPolynomialEval (P : Matrix R C (MvPolynomial I ℂ)) (x : I → ℝ) : Matrix R C ℂ :=
  P.map (MvPolynomial.eval (fun i => (x i : ℂ)))

omit [Fintype I] in
@[simp] theorem matrixPolynomialEval_apply (P : Matrix R C (MvPolynomial I ℂ))
    (x : I → ℝ) (a : R) (b : C) :
    matrixPolynomialEval P x a b = MvPolynomial.eval (fun i => (x i : ℂ)) (P a b) := rfl

theorem matrixPolynomialEval_entry_memLp (P : Matrix R C (MvPolynomial I ℂ))
    (a : R) (b : C) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => matrixPolynomialEval P x a b) p (realGaussianProduct I) :=
  realGaussianProduct_complex_polynomial_memLp (P a b) p hp

/-- A genuinely rectangular complex matrix series driven by independent standard real Gaussians. -/
def gaussianMatrixSeries (H : I → Matrix R C ℂ) (x : I → ℝ) : Matrix R C ℂ :=
  ∑ i, (x i : ℂ) • H i

def gaussianMatrixSeriesPolynomial (H : I → Matrix R C ℂ) : Matrix R C (MvPolynomial I ℂ) :=
  fun a b => ∑ i, MvPolynomial.C (H i a b) * MvPolynomial.X i

@[simp] theorem gaussianMatrixSeriesPolynomial_eval (H : I → Matrix R C ℂ) (x : I → ℝ) :
    matrixPolynomialEval (gaussianMatrixSeriesPolynomial H) x = gaussianMatrixSeries H x := by
  ext a b
  simp [matrixPolynomialEval, gaussianMatrixSeriesPolynomial, gaussianMatrixSeries,
    Matrix.sum_apply, mul_comm]

theorem gaussianMatrixSeries_entry_memLp (H : I → Matrix R C ℂ) (a : R) (b : C)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => gaussianMatrixSeries H x a b) p (realGaussianProduct I) := by
  simpa only [gaussianMatrixSeriesPolynomial_eval] using
    matrixPolynomialEval_entry_memLp (gaussianMatrixSeriesPolynomial H) a b p hp

section Trace
variable [Fintype N] [DecidableEq N]

omit [Fintype I] [DecidableEq N] in
@[simp] theorem matrixPolynomialEval_trace (P : Matrix N N (MvPolynomial I ℂ)) (x : I → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (Matrix.trace P) =
      Matrix.trace (matrixPolynomialEval P x) := AddMonoidHom.map_trace _ _

omit [DecidableEq N] in
theorem matrixPolynomialEval_trace_memLp (P : Matrix N N (MvPolynomial I ℂ))
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => Matrix.trace (matrixPolynomialEval P x)) p (realGaussianProduct I) := by
  simpa only [matrixPolynomialEval_trace] using
    realGaussianProduct_complex_polynomial_memLp (Matrix.trace P) p hp

omit [DecidableEq N] in
/-- IBP on actual matrix traces; partial differentiation is entrywise on the matrix polynomial. -/
theorem matrixPolynomialEval_trace_ibp [DecidableEq I]
    (P : Matrix N N (MvPolynomial I ℂ)) (i : I) :
    ∫ x, (x i : ℂ) * Matrix.trace (matrixPolynomialEval P x) ∂realGaussianProduct I =
      ∫ x, Matrix.trace (matrixPolynomialEval (P.map (MvPolynomial.pderiv i)) x)
        ∂realGaussianProduct I := by
  have h := realGaussianProduct_complex_polynomial_ibp (Matrix.trace P) i
  simpa only [matrixPolynomialEval_trace, AddMonoidHom.map_trace, matrixPolynomialEval] using h

/-- The polynomial whose value is `Tr (A (Σᵢ xᵢ Hᵢ)^k)`; no commutativity or Hermitian hypotheses. -/
def matrixSeriesTracePolynomial (H : I → Matrix N N ℂ) (A : Matrix N N ℂ) (k : Nat) :
    MvPolynomial I ℂ :=
  Matrix.trace (A.map MvPolynomial.C * (gaussianMatrixSeriesPolynomial H)^k)

theorem matrixSeriesTracePolynomial_eval (H : I → Matrix N N ℂ) (A : Matrix N N ℂ)
    (k : Nat) (x : I → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (matrixSeriesTracePolynomial H A k) =
      Matrix.trace (A * (gaussianMatrixSeries H x)^k) := by
  unfold matrixSeriesTracePolynomial
  rw [AddMonoidHom.map_trace, Matrix.map_mul, Matrix.map_pow]
  change Matrix.trace (((A.map MvPolynomial.C).map _) *
    (matrixPolynomialEval (gaussianMatrixSeriesPolynomial H) x)^k) = _
  rw [gaussianMatrixSeriesPolynomial_eval]
  congr 2
  ext a b
  simp

theorem gaussianMatrixSeries_trace_memLp (H : I → Matrix N N ℂ) (A : Matrix N N ℂ)
    (k : Nat) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => Matrix.trace (A*(gaussianMatrixSeries H x)^k))
      p (realGaussianProduct I) := by
  simpa only [matrixSeriesTracePolynomial_eval] using
    realGaussianProduct_complex_polynomial_memLp (matrixSeriesTracePolynomial H A k) p hp

theorem gaussianMatrixSeries_trace_hasDerivAt_coordinate [DecidableEq I]
    (H : I → Matrix N N ℂ) (A : Matrix N N ℂ) (k : Nat) (i : I) (x : I → ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.trace (A*(gaussianMatrixSeries H (Function.update x i t))^k))
      (MvPolynomial.eval (fun j => (x j : ℂ))
        (MvPolynomial.pderiv i (matrixSeriesTracePolynomial H A k))) (x i) := by
  simpa only [matrixSeriesTracePolynomial_eval] using
    complex_polynomial_hasDerivAt_coordinate (matrixSeriesTracePolynomial H A k) i x

/-- The actual analytic derivative of an arbitrary-order matrix trace polynomial is integrable. -/
theorem gaussianMatrixSeries_trace_deriv_integrable [DecidableEq I]
    (H : I → Matrix N N ℂ) (A : Matrix N N ℂ) (k : Nat) (i : I) :
    Integrable (fun x : I → ℝ => deriv (fun t : ℝ =>
      Matrix.trace (A*(gaussianMatrixSeries H (Function.update x i t))^k)) (x i))
      (realGaussianProduct I) := by
  simp_rw [(gaussianMatrixSeries_trace_hasDerivAt_coordinate H A k i _).deriv]
  exact realGaussianProduct_complex_polynomial_integrable _

/-- Gaussian IBP for actual noncommuting matrix-series traces, stated with the analytic derivative. -/
theorem gaussianMatrixSeries_trace_ibp [DecidableEq I]
    (H : I → Matrix N N ℂ) (A : Matrix N N ℂ) (k : Nat) (i : I) :
    ∫ x, (x i : ℂ)*Matrix.trace (A*(gaussianMatrixSeries H x)^k) ∂realGaussianProduct I =
      ∫ x : I → ℝ, deriv (fun t : ℝ =>
        Matrix.trace (A*(gaussianMatrixSeries H (Function.update x i t))^k)) (x i)
        ∂realGaussianProduct I := by
  simp_rw [(gaussianMatrixSeries_trace_hasDerivAt_coordinate H A k i _).deriv]
  simpa only [matrixSeriesTracePolynomial_eval] using
    realGaussianProduct_complex_polynomial_ibp (matrixSeriesTracePolynomial H A k) i

end Trace
end CertificationGaussian
