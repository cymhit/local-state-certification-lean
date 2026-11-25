import CertificationGaussian.HermitianTraceSandwich

noncomputable section
open Matrix Finset Unitary
open scoped BigOperators
namespace CertificationGaussian
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A spectral-basis diagonal entry is the actual Euclidean inner product against the operator. -/
theorem spectral_conjugate_diagonal (X V : Matrix N N ℂ) (hX : X.IsHermitian) (i : N) :
    (conjStarAlgAut ℂ (Matrix N N ℂ) (star hX.eigenvectorUnitary) V) i i =
      inner ℂ (hX.eigenvectorBasis i)
        (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V (hX.eigenvectorBasis i)) := by
  let U : Matrix N N ℂ := hX.eigenvectorUnitary
  rw [conjStarAlgAut_star_apply]
  change (Uᴴ*V*U) i i = _
  rw [Matrix.mul_assoc, ← inner_matrix_col_col U (V*U) i i]
  congr 1

/-- Each such real diagonal entry is bounded by the genuine Euclidean operator norm. -/
theorem spectral_conjugate_diagonal_le (X V : Matrix N N ℂ) (hX : X.IsHermitian) (i : N) :
    ((conjStarAlgAut ℂ (Matrix N N ℂ) (star hX.eigenvectorUnitary) V) i i).re ≤
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V‖ := by
  rw [spectral_conjugate_diagonal]
  have hn : ‖hX.eigenvectorBasis i‖ = 1 := hX.eigenvectorBasis.orthonormal.norm_eq_one i
  calc
    (inner ℂ (hX.eigenvectorBasis i) (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V
      (hX.eigenvectorBasis i))).re ≤
        ‖inner ℂ (hX.eigenvectorBasis i) (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V
          (hX.eigenvectorBasis i))‖ := Complex.re_le_norm _
    _ ≤ ‖hX.eigenvectorBasis i‖ * ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V
        (hX.eigenvectorBasis i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖hX.eigenvectorBasis i‖ *
        (‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V‖ * ‖hX.eigenvectorBasis i‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V).le_opNorm _)
        (norm_nonneg _)
    _ = _ := by rw [hn]; ring

/-- Weighted trace in the eigenbasis of X; V need not commute with X or be Hermitian. -/
theorem trace_mul_hermitian_power (X V : Matrix N N ℂ) (hX : X.IsHermitian) (k : Nat) :
    Matrix.trace (V*X^k) = ∑ i,
      (conjStarAlgAut ℂ (Matrix N N ℂ) (star hX.eigenvectorUnitary) V) i i *
        (hX.eigenvalues i : ℂ)^k := by
  rw [← trace_unitary_conjugation (star hX.eigenvectorUnitary) (V*X^k), map_mul, map_pow,
    hX.conjStarAlgAut_star_eigenvectorUnitary, Matrix.diagonal_pow]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Pi.pow_apply,
    Function.comp_apply]
  rfl

theorem trace_hermitian_power (X : Matrix N N ℂ) (hX : X.IsHermitian) (k : Nat) :
    Matrix.trace (X^k) = ∑ i, (hX.eigenvalues i : ℂ)^k := by
  simpa only [one_mul, map_one, Matrix.one_apply_eq, mul_one] using
    trace_mul_hermitian_power X 1 hX k

/-- No PSD or commutation hypothesis on V is needed: the even power of X supplies positivity. -/
theorem trace_mul_hermitian_even_power_le (X V : Matrix N N ℂ) (hX : X.IsHermitian)
    (k : Nat) (hk : Even k) :
    (Matrix.trace (V*X^k)).re ≤
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V‖*(Matrix.trace (X^k)).re := by
  rw [trace_mul_hermitian_power X V hX, trace_hermitian_power X hX]
  simp only [← Complex.ofReal_pow, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (spectral_conjugate_diagonal_le X V hX i) (hk.pow_nonneg _)

end CertificationGaussian
