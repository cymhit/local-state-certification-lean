import CertificationGaussian.GaussianMatrixTraceDerivative
import Mathlib.Data.Nat.Factorial.DoubleFactorial

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I N : Type*} [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]

/-- The variance matrix of a Hermitian Gaussian matrix series. -/
def gaussianMatrixCovariance (H : I → Matrix N N ℂ) : Matrix N N ℂ := ∑ i, (H i)^2

def gaussianTraceMoment (H : I → Matrix N N ℂ) (p : Nat) : ℝ :=
  ∫ x, (Matrix.trace ((gaussianMatrixSeries H x)^(2*p))).re ∂realGaussianProduct I

omit [DecidableEq I] [Fintype N] [DecidableEq N] in
theorem gaussianMatrixSeries_isHermitian (H : I → Matrix N N ℂ) (hH : ∀ i, (H i).IsHermitian)
    (x : I → ℝ) : (gaussianMatrixSeries H x).IsHermitian := by
  change (∑ i, (x i : ℂ) • H i)ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.conjTranspose_smul, (hH i).eq]

omit [DecidableEq I] in
theorem gaussianMatrixSeries_trace_power_integrable (H : I → Matrix N N ℂ) (k : Nat) :
    Integrable (fun x => Matrix.trace ((gaussianMatrixSeries H x)^k)) (realGaussianProduct I) := by
  have h := (gaussianMatrixSeries_trace_memLp H 1 k 1 (by simp)).integrable (by rfl)
  simpa only [one_mul] using h

omit [DecidableEq I] in
theorem gaussianMatrixSeries_coordinate_trace_integrable (H : I → Matrix N N ℂ)
    (A : Matrix N N ℂ) (k : Nat) (i : I) :
    Integrable (fun x => (x i : ℂ)*Matrix.trace (A*(gaussianMatrixSeries H x)^k))
      (realGaussianProduct I) := by
  have h := realGaussianProduct_complex_polynomial_integrable
    (MvPolynomial.X i * matrixSeriesTracePolynomial H A k)
  convert h using 1
  funext x
  simp only [map_mul, MvPolynomial.eval_X, matrixSeriesTracePolynomial_eval]

/-- The exact trace-moment integration-by-parts identity; every noncommuting insertion is present. -/
theorem gaussianMatrixSeries_trace_power_ibp (H : I → Matrix N N ℂ) (k : Nat) :
    ∫ x, Matrix.trace ((gaussianMatrixSeries H x)^(k+1)) ∂realGaussianProduct I =
      ∑ i, ∑ l ∈ Finset.range k, ∫ x, Matrix.trace
        (H i*(gaussianMatrixSeries H x)^(k.pred-l)*H i*(gaussianMatrixSeries H x)^l)
        ∂realGaussianProduct I := by
  have he (x : I → ℝ) : Matrix.trace ((gaussianMatrixSeries H x)^(k+1)) =
      ∑ i, (x i : ℂ)*Matrix.trace (H i*(gaussianMatrixSeries H x)^k) := by
    rw [pow_succ', gaussianMatrixSeries, Finset.sum_mul, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.smul_mul, Matrix.trace_smul]
    rfl
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => gaussianMatrixSeries_coordinate_trace_integrable H (H i) k i)]
  apply Finset.sum_congr rfl
  intro i _
  exact gaussianMatrixSeries_trace_ibp_expanded H (H i) k i

omit [DecidableEq I] in
/-- Pointwise bound on the even-order IBP insertion sum, using the true Euclidean operator norm. -/
theorem gaussianMatrixSeries_insertion_sum_le (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) (p : Nat) (x : I → ℝ) :
    (∑ i, ∑ l ∈ Finset.range (2*p+1), (Matrix.trace
      (H i*(gaussianMatrixSeries H x)^(2*p-l)*H i*(gaussianMatrixSeries H x)^l)).re) ≤
      (2*p+1:Nat) * ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖ *
        (Matrix.trace ((gaussianMatrixSeries H x)^(2*p))).re := by
  have hX := gaussianMatrixSeries_isHermitian H hH x
  calc
    _ ≤ ∑ i, ∑ _l ∈ Finset.range (2*p+1),
        (Matrix.trace ((H i)^2*(gaussianMatrixSeries H x)^(2*p))).re := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro l hl
      have hl' : l ≤ 2*p := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
      have h := hermitian_trace_sandwich (H i) (gaussianMatrixSeries H x) (hH i) hX
        (k := 2*p) (l := 2*p-l) (even_two.mul_right p) (Nat.sub_le _ _)
      rw [Nat.sub_sub_self hl'] at h
      exact (Complex.re_le_norm _).trans h
    _ = (2*p+1:Nat)*(Matrix.trace (gaussianMatrixCovariance H*(gaussianMatrixSeries H x)^(2*p))).re := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
      congr 1
      simp only [gaussianMatrixCovariance, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    _ ≤ _ := by
      have h := trace_mul_hermitian_even_power_le (gaussianMatrixSeries H x)
        (gaussianMatrixCovariance H) hX (2*p) (even_two.mul_right p)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ (2*p+1:Nat))

/-- The Gaussian Hermitian trace-moment recursion, including the first second moment p=0. -/
theorem gaussianTraceMoment_recursion (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) (p : Nat) :
    gaussianTraceMoment H (p+1) ≤ (2*p+1:Nat) *
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖ * gaussianTraceMoment H p := by
  have he := congrArg Complex.re (gaussianMatrixSeries_trace_power_ibp H (2*p+1))
  have hint (i : I) (l : Nat) := gaussianMatrixSeries_sandwich_integrable H (H i) (H i) (2*p-l) l
  have hintR (i : I) (l : Nat) : Integrable (fun x =>
      (Matrix.trace (H i*(gaussianMatrixSeries H x)^(2*p-l)*H i*(gaussianMatrixSeries H x)^l)).re)
      (realGaussianProduct I) := (hint i l).re
  have hpow := gaussianMatrixSeries_trace_power_integrable H (2*(p+1))
  have hi : Integrable (fun x => ∑ i, ∑ l ∈ Finset.range (2*p+1),
      (Matrix.trace (H i*(gaussianMatrixSeries H x)^(2*p-l)*H i*(gaussianMatrixSeries H x)^l)).re)
      (realGaussianProduct I) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => hintR i l))
  have he' : gaussianTraceMoment H (p+1) = ∫ x,
      (∑ i, ∑ l ∈ Finset.range (2*p+1), (Matrix.trace
        (H i*(gaussianMatrixSeries H x)^(2*p-l)*H i*(gaussianMatrixSeries H x)^l)).re)
        ∂realGaussianProduct I := by
    unfold gaussianTraceMoment
    have hre : (∫ x, (Matrix.trace ((gaussianMatrixSeries H x)^(2*(p+1)))).re
        ∂realGaussianProduct I) =
        (∫ x, Matrix.trace ((gaussianMatrixSeries H x)^(2*(p+1))) ∂realGaussianProduct I).re :=
      integral_re hpow
    rw [hre]
    rw [show 2*(p+1)= (2*p+1)+1 by omega]
    rw [he]
    simp only [Complex.re_sum, Nat.pred_succ]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => hintR i l))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun l _ => hintR i l)]
    apply Finset.sum_congr rfl
    intro l _
    exact (integral_re (hint i l)).symm
  rw [he']
  have hr := (gaussianMatrixSeries_trace_power_integrable H (2*p)).re.const_mul
    ((2*p+1:Nat)*‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖)
  have h := integral_mono hi hr (gaussianMatrixSeries_insertion_sum_le H hH p)
  rw [integral_const_mul] at h
  exact h

omit [DecidableEq I] in
@[simp] theorem gaussianTraceMoment_zero (H : I → Matrix N N ℂ) :
    gaussianTraceMoment H 0 = (Fintype.card N : ℝ) := by
  simp [gaussianTraceMoment, Matrix.trace_one]

omit [DecidableEq I] in
theorem gaussianTraceMoment_nonneg (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) (p : Nat) : 0 ≤ gaussianTraceMoment H p := by
  apply integral_nonneg
  intro x
  change 0 ≤ (Matrix.trace ((gaussianMatrixSeries H x)^(2*p))).re
  rw [trace_hermitian_power _ (gaussianMatrixSeries_isHermitian H hH x)]
  simp only [← Complex.ofReal_pow, Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun _ _ => (even_two.mul_right p).pow_nonneg _)

/-- The exact closed trace-moment bound, including p=0 and the empty matrix dimension. -/
theorem gaussianTraceMoment_bound (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) (p : Nat) :
    gaussianTraceMoment H p ≤ (Fintype.card N : ℝ) * (Nat.doubleFactorial (2*p-1) : ℝ) *
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖^p := by
  induction p with
  | zero => simp
  | succ p ih =>
    calc
      _ ≤ (2*p+1:Nat)*‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)
          (gaussianMatrixCovariance H)‖*gaussianTraceMoment H p := gaussianTraceMoment_recursion H hH p
      _ ≤ (2*p+1:Nat)*‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)
          (gaussianMatrixCovariance H)‖*((Fintype.card N : ℝ)*(Nat.doubleFactorial (2*p-1) : ℝ)*
          ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖^p) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by
        rw [show 2*(p+1)-1=2*p+1 by omega, Nat.doubleFactorial_add_one, Nat.cast_mul, pow_succ]
        ring

/-- Odd double factorial as a finite product, with the p=0 empty product convention. -/
theorem odd_doubleFactorial_eq_prod (p : Nat) :
    Nat.doubleFactorial (2*p-1) = ∏ j ∈ Finset.range p, (2*j+1) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [show 2*(p+1)-1=2*p+1 by omega, Nat.doubleFactorial_add_one,
      ih, Finset.prod_range_succ, mul_comm]

/-- A convenient coarse version for the later Gaussian operator-norm expectation estimate. -/
theorem gaussianTraceMoment_bound_pow (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) (p : Nat) :
    gaussianTraceMoment H p ≤ (Fintype.card N : ℝ)*(2*p:Nat)^p *
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖^p := by
  have hc : Nat.doubleFactorial (2*p-1) ≤ (2*p)^p := by
    rw [odd_doubleFactorial_eq_prod]
    calc
      _ ≤ ∏ _j ∈ Finset.range p, (2*p) := by
        apply Finset.prod_le_prod
        intro j hj
        have := Finset.mem_range.mp hj
        omega
      _ = _ := by simp
  exact (gaussianTraceMoment_bound H hH p).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (Nat.cast_nonneg _)) (by positivity))

end CertificationGaussian
