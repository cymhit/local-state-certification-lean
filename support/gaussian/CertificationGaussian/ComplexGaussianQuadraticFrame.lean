import CertificationGaussian.ComplexGaussianQuadraticCovariance
import CertificationGaussian.HermitianTraceSandwich
import Mathlib.Probability.Moments.Variance

/-! # Finite matrix ensembles and their actual Gaussian frame variance

The frame acts on the real Hilbert space of matrix entries with the
Hilbert–Schmidt norm. No orthogonal-basis or commutativity restriction is used.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators
namespace CertificationGaussian

section HilbertFrame
variable {O E : Type*} [Fintype O] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual weighted frame operator on a real Hilbert space. -/
def finiteHilbertFrame (w : O → ℝ) (v : O → E) : E →L[ℝ] E :=
  ∑ s, w s • InnerProductSpace.rankOne ℝ (v s) (v s)

theorem finiteHilbertFrame_inner (w : O → ℝ) (v : O → E) (x y : E) :
    inner ℝ (finiteHilbertFrame w v x) y =
      ∑ s, w s * (inner ℝ (v s) x * inner ℝ (v s) y) := by
  simp [finiteHilbertFrame, sum_inner, real_inner_smul_left]

theorem finiteHilbertFrame_inner_self (w : O → ℝ) (v : O → E) (x : E) :
    inner ℝ x (finiteHilbertFrame w v x) = ∑ s, w s * inner ℝ (v s) x ^ 2 := by
  rw [real_inner_comm, finiteHilbertFrame_inner]
  simp [pow_two]

/-- Quadratic-form control gives the operator norm of the actual frame. -/
theorem finiteHilbertFrame_norm_le (w : O → ℝ) (hw : ∀ s, 0 ≤ w s)
    (v : O → E) {c : ℝ} (hc : 0 ≤ c)
    (hquad : ∀ x, ∑ s, w s * inner ℝ (v s) x ^ 2 ≤ c * ‖x‖ ^ 2) :
    ‖finiteHilbertFrame w v‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hc
  intro x y hx hy
  change inner ℝ (finiteHilbertFrame w v x) y ≤ c
  rw [finiteHilbertFrame_inner]
  have hxy : (∑ s, w s * (inner ℝ (v s) x * inner ℝ (v s) y)) ≤
      ((∑ s, w s * inner ℝ (v s) x ^ 2) +
        (∑ s, w s * inner ℝ (v s) y ^ 2)) / 2 := by
    calc
      _ ≤ ∑ s, w s * ((inner ℝ (v s) x ^ 2 + inner ℝ (v s) y ^ 2) / 2) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (hw s)
        nlinarith [sq_nonneg (inner ℝ (v s) x - inner ℝ (v s) y)]
      _ = _ := by simp only [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
  have hqx := hquad x
  have hqy := hquad y
  rw [hx, one_pow, mul_one] at hqx
  rw [hy, one_pow, mul_one] at hqy
  linarith

/-- The frame second moment is controlled by its operator norm times its trace. -/
theorem finiteHilbertFrame_second_le (w : O → ℝ) (hw : ∀ s, 0 ≤ w s) (v : O → E) :
    (∑ s, ∑ t, w s * w t * inner ℝ (v s) (v t) ^ 2) ≤
      ‖finiteHilbertFrame w v‖ * ∑ s, w s * ‖v s‖ ^ 2 := by
  calc
    _ = ∑ s, w s * inner ℝ (v s) (finiteHilbertFrame w v (v s)) := by
      simp only [finiteHilbertFrame_inner_self, Finset.mul_sum, ← mul_assoc]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      rw [real_inner_comm (v t) (v s)]
    _ ≤ ∑ s, w s * (‖finiteHilbertFrame w v‖ * ‖v s‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (hw s)
      calc
        _ ≤ ‖v s‖ * ‖finiteHilbertFrame w v (v s)‖ := real_inner_le_norm _ _
        _ ≤ ‖v s‖ * (‖finiteHilbertFrame w v‖ * ‖v s‖) :=
          mul_le_mul_of_nonneg_left ((finiteHilbertFrame w v).le_opNorm _) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring

/-- Applying a genuine bounded map to the ensemble transports its frame by congruence. -/
theorem finiteHilbertFrame_map [CompleteSpace E] (w : O → ℝ) (v : O → E)
    (R : E →L[ℝ] E) :
    finiteHilbertFrame w (fun s => R (v s)) =
      R.comp ((finiteHilbertFrame w v).comp (ContinuousLinearMap.adjoint R)) := by
  ext x
  simp [finiteHilbertFrame, InnerProductSpace.rankOne_apply,
    ContinuousLinearMap.adjoint_inner_right, map_sum]

theorem finiteHilbertFrame_map_norm [CompleteSpace E] (w : O → ℝ) (v : O → E)
    (R : E →L[ℝ] E) :
    ‖finiteHilbertFrame w (fun s => R (v s))‖ ≤
      ‖R‖ ^ 2 * ‖finiteHilbertFrame w v‖ := by
  rw [finiteHilbertFrame_map]
  calc
    _ ≤ ‖R‖ * ‖(finiteHilbertFrame w v).comp (ContinuousLinearMap.adjoint R)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖R‖ * (‖finiteHilbertFrame w v‖ * ‖ContinuousLinearMap.adjoint R‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by simp only [LinearIsometryEquiv.norm_map]; ring

end HilbertFrame

section MatrixEnsemble
variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

/-- Matrix entries in the Hilbert–Schmidt Hilbert space, with real scalars for frames. -/
def matrixHilbertSchmidt (A : Matrix I I ℂ) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

omit [DecidableEq I] in
theorem matrixHilbertSchmidt_inner (A B : Matrix I I ℂ) (hA : A.IsHermitian) :
    inner ℝ (matrixHilbertSchmidt A) (matrixHilbertSchmidt B) = (A*B).trace.re := by
  change (∑ ij : I × I, (B ij.1 ij.2 * star (A ij.1 ij.2)).re) = _
  rw [← Complex.re_sum]
  congr 1
  simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (fun M : Matrix I I ℂ => M j i) hA.eq
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]
  simp [mul_comm]

theorem matrixHilbertSchmidt_norm_sq (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    ‖matrixHilbertSchmidt A‖ ^ 2 = (A^2).trace.re := by
  rw [← real_inner_self_eq_norm_sq, matrixHilbertSchmidt_inner A A hA, pow_two]

/-- The finite ensemble observable under the actual standard complex Gaussian. -/
def finiteQuadraticEnsemble (w : O → ℝ) (B : O → Matrix I I ℂ)
    (x : Fin 2 × I → ℝ) : ℝ :=
  ∑ s, w s * (complexGaussianCenteredQuadratic (B s) x).re ^ 2

local instance quadraticFramePairedGaussianProbability : IsProbabilityMeasure (pairedGaussian I) := by
  unfold pairedGaussian
  infer_instance

omit [DecidableEq I] in
theorem finiteQuadraticEnsemble_memLp (w : O → ℝ) (B : O → Matrix I I ℂ)
    (hB : ∀ s, (B s).IsHermitian) :
    MemLp (finiteQuadraticEnsemble w B) 2 (pairedGaussian I) := by
  exact memLp_finsetSum _ (fun s _ =>
    (complexGaussianCenteredQuadratic_real_square_memLp (B s) (hB s)).const_mul (w s))

theorem finiteQuadraticEnsemble_mean (w : O → ℝ) (B : O → Matrix I I ℂ)
    (hB : ∀ s, (B s).IsHermitian) :
    (∫ x, finiteQuadraticEnsemble w B x ∂pairedGaussian I) =
      ∑ s, w s * ((B s)^2).trace.re := by
  unfold finiteQuadraticEnsemble
  rw [integral_finsetSum]
  · simp only [integral_const_mul, complexGaussian_centered_quadratic_real_second _ (hB _)]
  · intro s _
    exact ((complexGaussianCenteredQuadratic_real_square_memLp (B s) (hB s)).integrable
      (by norm_num)).const_mul (w s)

theorem finiteQuadraticEnsemble_variance (w : O → ℝ) (B : O → Matrix I I ℂ)
    (hB : ∀ s, (B s).IsHermitian) :
    variance (finiteQuadraticEnsemble w B) (pairedGaussian I) =
      ∑ s, ∑ t, w s * w t *
        (2 * (B s * B t).trace.re ^ 2 + 2 * (B s * B t * B s * B t).trace.re +
          4 * ((B s)^2 * (B t)^2).trace.re) := by
  unfold finiteQuadraticEnsemble
  rw [variance_fun_sum]
  · simp only [covariance_const_mul_left, covariance_const_mul_right,
      complexGaussian_centered_quadratic_square_covariance _ _ (hB _) (hB _)]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  · intro s
    exact (complexGaussianCenteredQuadratic_real_square_memLp (B s) (hB s)).const_mul (w s)

/-- The frame of the actual Hermitian matrix ensemble in the real HS space. -/
def finiteMatrixFrame (w : O → ℝ) (B : O → Matrix I I ℂ) :
    EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I) :=
  finiteHilbertFrame w (fun s => matrixHilbertSchmidt (B s))

/-- The actual matrix second moment, including signed Hermitian B_s. -/
def finiteMatrixSecondMoment (w : O → ℝ) (B : O → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ s, (w s : ℂ) • (B s)^2

theorem finiteMatrixFrame_pairing_bound (w : O → ℝ) (hw : ∀ s, 0 ≤ w s)
    (B : O → Matrix I I ℂ) (hB : ∀ s, (B s).IsHermitian) :
    (∑ s, ∑ t, w s * w t * (B s * B t).trace.re ^ 2) ≤
      ‖finiteMatrixFrame w B‖ * ∑ s, w s * ((B s)^2).trace.re := by
  simpa only [finiteMatrixFrame, matrixHilbertSchmidt_inner _ _ (hB _),
    matrixHilbertSchmidt_norm_sq _ (hB _)] using
    finiteHilbertFrame_second_le w hw (fun s => matrixHilbertSchmidt (B s))

theorem finiteMatrixSecondMoment_trace_square (w : O → ℝ) (B : O → Matrix I I ℂ) :
    ((finiteMatrixSecondMoment w B)^2).trace.re =
      ∑ s, ∑ t, w s * w t * ((B s)^2 * (B t)^2).trace.re := by
  rw [pow_two]
  simp only [finiteMatrixSecondMoment, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  simp only [Finset.mul_sum, ← mul_assoc]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [Matrix.trace_mul_comm ((B t)^2) ((B s)^2)]

/-- The actual Gaussian variance is controlled by the actual frame and matrix second moment. -/
theorem finiteQuadraticEnsemble_variance_le (w : O → ℝ) (hw : ∀ s, 0 ≤ w s)
    (B : O → Matrix I I ℂ) (hB : ∀ s, (B s).IsHermitian) :
    variance (finiteQuadraticEnsemble w B) (pairedGaussian I) ≤
      2 * ‖finiteMatrixFrame w B‖ * (∑ s, w s * ((B s)^2).trace.re) +
        6 * ((finiteMatrixSecondMoment w B)^2).trace.re := by
  have hcycle (s t : O) : (B s * B t * B s * B t).trace.re ≤
      ((B s)^2 * (B t)^2).trace.re := by
    apply (Complex.re_le_norm _).trans
    simpa only [show 2 - 1 = (1 : ℕ) from rfl, pow_one] using
      hermitian_trace_sandwich (B s) (B t) (hB s) (hB t)
        (k := 2) (l := 1) (by decide) (by omega)
  have hbound : variance (finiteQuadraticEnsemble w B) (pairedGaussian I) ≤
      ∑ s, ∑ t, w s * w t *
        (2 * (B s * B t).trace.re ^ 2 + 6 * ((B s)^2 * (B t)^2).trace.re) := by
    rw [finiteQuadraticEnsemble_variance w B hB]
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro t _
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw s) (hw t))
    linarith [hcycle s t]
  have hexpand : (∑ s, ∑ t, w s * w t *
      (2 * (B s * B t).trace.re ^ 2 + 6 * ((B s)^2 * (B t)^2).trace.re)) =
      2 * (∑ s, ∑ t, w s * w t * (B s * B t).trace.re ^ 2) +
        6 * (∑ s, ∑ t, w s * w t * ((B s)^2 * (B t)^2).trace.re) := by
    simp_rw [show ∀ s t, w s * w t *
        (2 * (B s * B t).trace.re ^ 2 + 6 * ((B s)^2 * (B t)^2).trace.re) =
        2 * (w s * w t * (B s * B t).trace.re ^ 2) +
          6 * (w s * w t * ((B s)^2 * (B t)^2).trace.re) from fun s t => by ring]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexpand, ← finiteMatrixSecondMoment_trace_square] at hbound
  have hp := finiteMatrixFrame_pairing_bound w hw B hB
  nlinarith

/-- The scalar variance estimate once the separately proved frame and matrix moments are supplied. -/
theorem finiteQuadraticEnsemble_variance_le_scalar (w : O → ℝ) (hw : ∀ s, 0 ≤ w s)
    (B : O → Matrix I I ℂ) (hB : ∀ s, (B s).IsHermitian)
    (v L : ℝ) (hv : 0 ≤ v)
    (htrace : ∑ s, w s * ((B s)^2).trace.re = v)
    (hsecond : finiteMatrixSecondMoment w B =
      ((v / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ))
    (hframe : ‖finiteMatrixFrame w B‖ ≤ L^2 / (Fintype.card I : ℝ)) :
    variance (finiteQuadraticEnsemble w B) (pairedGaussian I) ≤
      (2 * L^2 * v + 6 * v^2) / (Fintype.card I : ℝ) := by
  have h := finiteQuadraticEnsemble_variance_le w hw B hB
  rw [htrace, hsecond] at h
  have hs : ((((v / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ))^2).trace.re =
      v^2 / (Fintype.card I : ℝ) := by
    by_cases hd : (Fintype.card I : ℝ) = 0
    · simp [hd]
    · simp only [pow_two, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
        mul_zero, sub_zero]
      field_simp
  rw [hs] at h
  calc
    _ ≤ 2 * ‖finiteMatrixFrame w B‖ * v + 6 * (v^2 / (Fintype.card I : ℝ)) := h
    _ ≤ 2 * (L^2 / (Fintype.card I : ℝ)) * v + 6 * (v^2 / (Fintype.card I : ℝ)) := by
      gcongr
    _ = _ := by ring

theorem finiteQuadraticEnsemble_variance_le_eight (w : O → ℝ) (hw : ∀ s, 0 ≤ w s)
    (B : O → Matrix I I ℂ) (hB : ∀ s, (B s).IsHermitian)
    (v L : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L^2)
    (htrace : ∑ s, w s * ((B s)^2).trace.re = v)
    (hsecond : finiteMatrixSecondMoment w B =
      ((v / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ))
    (hframe : ‖finiteMatrixFrame w B‖ ≤ L^2 / (Fintype.card I : ℝ)) :
    variance (finiteQuadraticEnsemble w B) (pairedGaussian I) ≤
      8 * L^2 * v / (Fintype.card I : ℝ) := by
  apply (finiteQuadraticEnsemble_variance_le_scalar w hw B hB v L hv htrace hsecond hframe).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hvL hv]

end MatrixEnsemble
end CertificationGaussian
