import CertificationGaussian.GaussianMatrixPolynomial
import CertificationGaussian.HermitianTraceBound
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I N : Type*} [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]

/-- The actual matrix derivative along coordinate i is the coefficient matrix H_i. -/
theorem gaussianMatrixSeries_hasDerivAt_coordinate (H : I → Matrix N N ℂ)
    (i : I) (x : I → ℝ) :
    HasDerivAt (fun t : ℝ => gaussianMatrixSeries H (Function.update x i t)) (H i) (x i) := by
  have h (j : I) : HasDerivAt (fun t : ℝ => (Function.update x i t j : ℂ) • H j)
      (if j=i then H j else 0) (x i) := by
    by_cases hj : j=i
    · subst j
      have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 (x i) :=
        (Complex.ofRealCLM.hasFDerivAt (x := x i)).hasDerivAt
      simpa only [Function.update_self, ite_true, one_smul] using hid.smul_const (H i)
    · simpa [Function.update_of_ne hj, hj] using
        hasDerivAt_const (x i) ((x j : ℂ) • H j)
  simpa only [gaussianMatrixSeries, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => h j)

/-- Noncommutative power differentiation: every placement of H_i is retained. -/
theorem gaussianMatrixSeries_trace_hasDerivAt_expanded (H : I → Matrix N N ℂ)
    (A : Matrix N N ℂ) (k : Nat) (i : I) (x : I → ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.trace (A*(gaussianMatrixSeries H (Function.update x i t))^k))
      (∑ l ∈ Finset.range k, Matrix.trace
        (A*(gaussianMatrixSeries H x)^(k.pred-l)*H i*(gaussianMatrixSeries H x)^l)) (x i) := by
  let tr : Matrix N N ℂ →L[ℝ] ℂ := (Matrix.traceLinearMap N ℝ ℂ).toContinuousLinearMap
  have h := tr.hasFDerivAt.comp_hasDerivAt (x i)
    (((gaussianMatrixSeries_hasDerivAt_coordinate H i x).fun_pow' k).const_mul A)
  convert h using 1
  · rfl
  · change _ = Matrix.trace (A * ∑ l ∈ Finset.range k,
      (gaussianMatrixSeries H (Function.update x i (x i)))^(k.pred-l)*H i*
        (gaussianMatrixSeries H (Function.update x i (x i)))^l)
    simp only [Function.update_eq_self, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]

omit [DecidableEq I] in
/-- All noncommutative sandwich traces used by the Gaussian IBP expansion are integrable. -/
theorem gaussianMatrixSeries_sandwich_integrable (H : I → Matrix N N ℂ)
    (A B : Matrix N N ℂ) (l m : Nat) :
    Integrable (fun x => Matrix.trace
      (A*(gaussianMatrixSeries H x)^l*B*(gaussianMatrixSeries H x)^m)) (realGaussianProduct I) := by
  let P := A.map MvPolynomial.C * (gaussianMatrixSeriesPolynomial H)^l *
    B.map MvPolynomial.C * (gaussianMatrixSeriesPolynomial H)^m
  have h := (matrixPolynomialEval_trace_memLp P 1 (by simp)).integrable (by rfl)
  convert h using 1
  funext x
  dsimp [P, matrixPolynomialEval]
  simp only [Matrix.map_mul, Matrix.map_pow]
  change _ = Matrix.trace (((A.map MvPolynomial.C).map _) *
    (matrixPolynomialEval (gaussianMatrixSeriesPolynomial H) x)^l *
    ((B.map MvPolynomial.C).map _) *
    (matrixPolynomialEval (gaussianMatrixSeriesPolynomial H) x)^m)
  rw [gaussianMatrixSeriesPolynomial_eval]
  have hc (D : Matrix N N ℂ) : (D.map MvPolynomial.C).map
      (MvPolynomial.eval (fun j => (x j : ℂ))) = D := by
    ext a b
    simp
  rw [hc A, hc B]

/-- The fully expanded Gaussian trace IBP identity, for any complex coefficient matrices. -/
theorem gaussianMatrixSeries_trace_ibp_expanded (H : I → Matrix N N ℂ)
    (A : Matrix N N ℂ) (k : Nat) (i : I) :
    ∫ x, (x i : ℂ)*Matrix.trace (A*(gaussianMatrixSeries H x)^k) ∂realGaussianProduct I =
      ∑ l ∈ Finset.range k, ∫ x, Matrix.trace
        (A*(gaussianMatrixSeries H x)^(k.pred-l)*H i*(gaussianMatrixSeries H x)^l)
        ∂realGaussianProduct I := by
  rw [gaussianMatrixSeries_trace_ibp]
  simp_rw [(gaussianMatrixSeries_trace_hasDerivAt_expanded H A k i _).deriv]
  exact integral_finsetSum _ (fun l _ => gaussianMatrixSeries_sandwich_integrable H A (H i) _ _)

end CertificationGaussian
