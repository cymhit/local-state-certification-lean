import CertificationGaussian.ComplexGaussianQuadraticFrame
import CertificationGaussian.RankOneWickContraction

/-! # The local POVM frame bound from an actual rank-one resolution

The vectors need not be orthogonal or distinct. The first matrix moment,
unit norm and positive weights imply the Hilbert–Schmidt frame norm bound.
-/

noncomputable section
open Matrix Finset
open scoped BigOperators
namespace CertificationGaussian
variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

omit [Fintype I] [DecidableEq I] in
theorem vectorRankOne_self_hermitian (u : EuclideanSpace ℂ I) :
    (vectorRankOne u u).IsHermitian := by
  change (vectorRankOne u u).conjTranspose = vectorRankOne u u
  ext i j
  simp [vectorRankOne, Matrix.conjTranspose_apply, mul_comm]

omit [DecidableEq I] in
theorem vectorRankOne_trace_pairing (A : Matrix I I ℂ) (u : EuclideanSpace ℂ I) :
    (A * vectorRankOne u u).trace = sphereQuadraticForm A u := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vectorRankOne, sphereQuadraticForm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vectorRankOne_star_square_trace (A : Matrix I I ℂ) (u : EuclideanSpace ℂ I) :
    (A.conjTranspose * A * vectorRankOne u u).trace.re =
      ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A u‖ ^ 2 := by
  rw [vectorRankOne_trace_pairing, sphereQuadraticForm_eq_inner]
  have hstar : A.conjTranspose = star A := rfl
  rw [hstar, map_mul, map_star]
  change (inner ℂ u (ContinuousLinearMap.adjoint
    (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A)
    (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A u))).re = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp [pow_two]

theorem vectorRankOne_trace_sq_le (A : Matrix I I ℂ) (u : EuclideanSpace ℂ I)
    (hu : ‖u‖ = 1) :
    (A * vectorRankOne u u).trace.re ^ 2 ≤
      (A.conjTranspose * A * vectorRankOne u u).trace.re := by
  rw [vectorRankOne_star_square_trace, vectorRankOne_trace_pairing, sphereQuadraticForm_eq_inner]
  have h := (Complex.abs_re_le_norm
    (inner ℂ u (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A u))).trans
    (norm_inner_le_norm u (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A u))
  rw [hu, one_mul] at h
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h

omit [DecidableEq I] in
theorem matrixHilbertSchmidt_star_square (A : Matrix I I ℂ) :
    (A.conjTranspose * A).trace.re = ‖matrixHilbertSchmidt A‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, matrixHilbertSchmidt, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]

/-- No orthogonality is assumed: the first moment alone gives the local frame bound. -/
theorem finiteRankOneFrame_norm_le (w : O → ℝ) (hw : ∀ s, 0 ≤ w s)
    (u : O → EuclideanSpace ℂ I) (hu : ∀ s, ‖u s‖ = 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hmean : (∑ s, (w s : ℂ) • vectorRankOne (u s) (u s)) =
      (c : ℂ) • (1 : Matrix I I ℂ)) :
    ‖finiteMatrixFrame w (fun s => vectorRankOne (u s) (u s))‖ ≤ c := by
  apply finiteHilbertFrame_norm_le w hw _ hc
  intro x
  let A : Matrix I I ℂ := fun i j => x (i,j)
  have hx : matrixHilbertSchmidt A = x := rfl
  have hsum : (∑ s, w s * (A.conjTranspose * A * vectorRankOne (u s) (u s)).trace.re) =
      c * ‖x‖ ^ 2 := by
    have hm := congrArg (fun M : Matrix I I ℂ => (A.conjTranspose * A * M).trace.re) hmean
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, mul_one] at hm
    rw [matrixHilbertSchmidt_star_square, hx] at hm
    exact hm
  calc
    _ = ∑ s, w s * (A * vectorRankOne (u s) (u s)).trace.re ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← hx, matrixHilbertSchmidt_inner _ A (vectorRankOne_self_hermitian _),
        Matrix.trace_mul_comm]
    _ ≤ ∑ s, w s * (A.conjTranspose * A * vectorRankOne (u s) (u s)).trace.re := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (vectorRankOne_trace_sq_le A (u s) (hu s)) (hw s)
    _ = _ := hsum

theorem finiteRankOneFrame_map_norm_le (w : O → ℝ) (hw : ∀ s, 0 ≤ w s)
    (u : O → EuclideanSpace ℂ I) (hu : ∀ s, ‖u s‖ = 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hmean : (∑ s, (w s : ℂ) • vectorRankOne (u s) (u s)) =
      (c : ℂ) • (1 : Matrix I I ℂ))
    (R : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)) :
    ‖finiteHilbertFrame w (fun s => R (matrixHilbertSchmidt (vectorRankOne (u s) (u s))))‖ ≤
      ‖R‖ ^ 2 * c := by
  apply (finiteHilbertFrame_map_norm w _ R).trans
  exact mul_le_mul_of_nonneg_left (finiteRankOneFrame_norm_le w hw u hu hc hmean) (sq_nonneg _)

theorem vectorRankOne_self_sq (u : EuclideanSpace ℂ I) (hu : ‖u‖ = 1) :
    (vectorRankOne u u)^2 = vectorRankOne u u := by
  rw [pow_two, vectorRankOne_mul, inner_self_eq_norm_sq_to_K, hu]
  simp

omit [DecidableEq I] in
theorem vectorRankOne_self_trace (u : EuclideanSpace ℂ I) (hu : ‖u‖ = 1) :
    (vectorRankOne u u).trace = 1 := by
  rw [vectorRankOne_trace, inner_self_eq_norm_sq_to_K, hu]
  simp

/-- Radius zero for every finite rank-one POVM, without an orthogonal-basis restriction. -/
theorem finiteRankOneGaussian_zeroRadius_variance (w : O → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hwone : ∑ s, w s = 1)
    (u : O → EuclideanSpace ℂ I) (hu : ∀ s, ‖u s‖ = 1)
    (hmean : (∑ s, (w s : ℂ) • vectorRankOne (u s) (u s)) =
      ((1 / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ)) :
    ProbabilityTheory.variance
      (finiteQuadraticEnsemble w (fun s => vectorRankOne (u s) (u s))) (pairedGaussian I) ≤
        8 / (Fintype.card I : ℝ) := by
  have ht : (∑ s, w s * ((vectorRankOne (u s) (u s))^2).trace.re) = 1 := by
    simp only [vectorRankOne_self_sq _ (hu _), vectorRankOne_self_trace _ (hu _),
      Complex.one_re, mul_one]
    exact hwone
  have hs : finiteMatrixSecondMoment w (fun s => vectorRankOne (u s) (u s)) =
      ((1 / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ) := by
    simpa only [finiteMatrixSecondMoment, vectorRankOne_self_sq _ (hu _)] using hmean
  have hf := finiteRankOneFrame_norm_le w hw u hu
    (c := 1 / (Fintype.card I : ℝ)) (by positivity) hmean
  have h := finiteQuadraticEnsemble_variance_le_eight w hw
    (fun s => vectorRankOne (u s) (u s)) (fun s => vectorRankOne_self_hermitian _)
    1 1 (by norm_num) (by norm_num) ht hs (by simpa only [one_pow] using hf)
  simpa only [one_pow, mul_one] using h

end CertificationGaussian
