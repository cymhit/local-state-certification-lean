import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

noncomputable section
open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- The actual rectangular operator between complex Euclidean spaces. -/
def rectangularEuclideanCLM (B : Matrix R C ℂ) : EuclideanSpace ℂ C →L[ℂ] EuclideanSpace ℂ R :=
  (Matrix.toEuclideanLin B).toContinuousLinearMap

omit [DecidableEq R] in
@[simp] theorem rectangularEuclideanCLM_toLp (B : Matrix R C ℂ) (x : C → ℂ) :
    rectangularEuclideanCLM B (WithLp.toLp 2 x) = WithLp.toLp 2 (B *ᵥ x) := rfl

omit [DecidableEq R] in
/-- This is the L2 operator norm, rather than the entrywise matrix norm. -/
theorem rectangularEuclideanCLM_norm (B : Matrix R C ℂ) : ‖rectangularEuclideanCLM B‖ = ‖B‖ := rfl

omit [DecidableEq R] [DecidableEq C] in
theorem euclidean_sum_elim_norm_sq (x : R → ℂ) (y : C → ℂ) :
    ‖(WithLp.toLp 2 (Sum.elim x y) : EuclideanSpace ℂ (R ⊕ C))‖^2 =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ R)‖^2 + ‖(WithLp.toLp 2 y : EuclideanSpace ℂ C)‖^2 := by
  simp [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]

omit [DecidableEq R] [DecidableEq C] in
theorem euclidean_sum_norm_sq (x : R ⊕ C → ℂ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (R ⊕ C))‖^2 =
      ‖(WithLp.toLp 2 (x ∘ Sum.inl) : EuclideanSpace ℂ R)‖^2 +
        ‖(WithLp.toLp 2 (x ∘ Sum.inr) : EuclideanSpace ℂ C)‖^2 := by
  simp [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]

omit [DecidableEq R] in
/-- A squared pointwise Euclidean estimate controls the genuine rectangular operator norm. -/
theorem matrix_l2_norm_le_of_sq (B : Matrix R C ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x : C → ℂ, ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℂ R)‖^2 ≤
      c^2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ C)‖^2) : ‖B‖ ≤ c := by
  rw [← rectangularEuclideanCLM_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hx := h (WithLp.ofLp x)
  change ‖rectangularEuclideanCLM B x‖^2 ≤ c^2*‖x‖^2 at hx
  nlinarith [norm_nonneg (rectangularEuclideanCLM B x), mul_nonneg hc (norm_nonneg x)]

/-- The Hermitian dilation of an arbitrary rectangular complex matrix. -/
def hermitianDilation (B : Matrix R C ℂ) : Matrix (R ⊕ C) (R ⊕ C) ℂ :=
  Matrix.fromBlocks 0 B Bᴴ 0

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
theorem hermitianDilation_isHermitian (B : Matrix R C ℂ) : (hermitianDilation B).IsHermitian := by
  change (Matrix.fromBlocks 0 B Bᴴ 0)ᴴ = _
  simp [Matrix.fromBlocks_conjTranspose, hermitianDilation]

theorem hermitianDilation_sq (B : Matrix R C ℂ) :
    (hermitianDilation B)^2 = Matrix.fromBlocks (B*Bᴴ) 0 0 (Bᴴ*B) := by
  simp [hermitianDilation, pow_two, Matrix.fromBlocks_multiply]

/-- The upper half of the dilation norm identity, with both dimensions possibly empty. -/
theorem hermitianDilation_norm_le (B : Matrix R C ℂ) : ‖hermitianDilation B‖ ≤ ‖B‖ := by
  apply matrix_l2_norm_le_of_sq _ _ (norm_nonneg _)
  intro x
  simp only [hermitianDilation, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero]
  rw [euclidean_sum_elim_norm_sq, euclidean_sum_norm_sq]
  have hB := Matrix.l2_opNorm_mulVec B (WithLp.toLp 2 (x ∘ Sum.inr))
  have hBs := Matrix.l2_opNorm_mulVec Bᴴ (WithLp.toLp 2 (x ∘ Sum.inl))
  rw [Matrix.l2_opNorm_conjTranspose] at hBs
  have hB2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hBs2 := pow_le_pow_left₀ (norm_nonneg _) hBs 2
  change ‖(WithLp.toLp 2 (B *ᵥ (x ∘ Sum.inr)) : EuclideanSpace ℂ R)‖^2 ≤
    (‖B‖*‖(WithLp.toLp 2 (x ∘ Sum.inr) : EuclideanSpace ℂ C)‖)^2 at hB2
  change ‖(WithLp.toLp 2 (Bᴴ *ᵥ (x ∘ Sum.inl)) : EuclideanSpace ℂ C)‖^2 ≤
    (‖B‖*‖(WithLp.toLp 2 (x ∘ Sum.inl) : EuclideanSpace ℂ R)‖)^2 at hBs2
  nlinarith

/-- The reverse inequality uses the actual isometric right summand, not a product sup norm. -/
theorem norm_le_hermitianDilation (B : Matrix R C ℂ) : ‖B‖ ≤ ‖hermitianDilation B‖ := by
  apply matrix_l2_norm_le_of_sq _ _ (norm_nonneg _)
  intro x
  have h := Matrix.l2_opNorm_mulVec (hermitianDilation B)
    (WithLp.toLp 2 (Sum.elim (0 : R → ℂ) x))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [hermitianDilation, Matrix.fromBlocks_mulVec, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add,
    add_zero, mul_pow] at h2
  change ‖(WithLp.toLp 2 (Sum.elim (B *ᵥ x) (0 : C → ℂ)) : EuclideanSpace ℂ (R ⊕ C))‖^2 ≤
    ‖hermitianDilation B‖^2 *
      ‖(WithLp.toLp 2 (Sum.elim (0 : R → ℂ) x) : EuclideanSpace ℂ (R ⊕ C))‖^2 at h2
  rw [euclidean_sum_elim_norm_sq, euclidean_sum_elim_norm_sq] at h2
  simpa using h2

/-- Exact operator norm preservation under Hermitian dilation. -/
theorem hermitianDilation_norm (B : Matrix R C ℂ) : ‖hermitianDilation B‖ = ‖B‖ :=
  le_antisymm (hermitianDilation_norm_le B) (norm_le_hermitianDilation B)

/-- The block diagonal norm upper bound uses the Euclidean orthogonal sum on both summands. -/
theorem matrix_l2_blockDiagonal_norm_le (A : Matrix R R ℂ) (B : Matrix C C ℂ) :
    ‖Matrix.fromBlocks A 0 0 B‖ ≤ max ‖A‖ ‖B‖ := by
  apply matrix_l2_norm_le_of_sq _ _ (le_trans (norm_nonneg A) (le_max_left _ _))
  intro x
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero]
  rw [euclidean_sum_elim_norm_sq, euclidean_sum_norm_sq]
  have hA := (Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (x ∘ Sum.inl))).trans
    (mul_le_mul_of_nonneg_right (le_max_left ‖A‖ ‖B‖) (norm_nonneg _))
  have hB := (Matrix.l2_opNorm_mulVec B (WithLp.toLp 2 (x ∘ Sum.inr))).trans
    (mul_le_mul_of_nonneg_right (le_max_right ‖A‖ ‖B‖) (norm_nonneg _))
  have hA2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hB2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  change ‖(WithLp.toLp 2 (A *ᵥ (x ∘ Sum.inl)) : EuclideanSpace ℂ R)‖^2 ≤
    ((max ‖A‖ ‖B‖)*‖(WithLp.toLp 2 (x ∘ Sum.inl) : EuclideanSpace ℂ R)‖)^2 at hA2
  change ‖(WithLp.toLp 2 (B *ᵥ (x ∘ Sum.inr)) : EuclideanSpace ℂ C)‖^2 ≤
    ((max ‖A‖ ‖B‖)*‖(WithLp.toLp 2 (x ∘ Sum.inr) : EuclideanSpace ℂ C)‖)^2 at hB2
  nlinarith

theorem matrix_l2_left_norm_le_blockDiagonal (A : Matrix R R ℂ) (B : Matrix C C ℂ) :
    ‖A‖ ≤ ‖Matrix.fromBlocks A 0 0 B‖ := by
  apply matrix_l2_norm_le_of_sq _ _ (norm_nonneg _)
  intro x
  have h := Matrix.l2_opNorm_mulVec (Matrix.fromBlocks A 0 0 B)
    (WithLp.toLp 2 (Sum.elim x (0 : C → ℂ)))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, mul_pow] at h2
  change ‖(WithLp.toLp 2 (Sum.elim (A *ᵥ x) (0 : C → ℂ)) : EuclideanSpace ℂ (R ⊕ C))‖^2 ≤
    ‖Matrix.fromBlocks A 0 0 B‖^2 *
      ‖(WithLp.toLp 2 (Sum.elim x (0 : C → ℂ)) : EuclideanSpace ℂ (R ⊕ C))‖^2 at h2
  rw [euclidean_sum_elim_norm_sq, euclidean_sum_elim_norm_sq] at h2
  simpa using h2

theorem matrix_l2_right_norm_le_blockDiagonal (A : Matrix R R ℂ) (B : Matrix C C ℂ) :
    ‖B‖ ≤ ‖Matrix.fromBlocks A 0 0 B‖ := by
  apply matrix_l2_norm_le_of_sq _ _ (norm_nonneg _)
  intro x
  have h := Matrix.l2_opNorm_mulVec (Matrix.fromBlocks A 0 0 B)
    (WithLp.toLp 2 (Sum.elim (0 : R → ℂ) x))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add, add_zero, mul_pow] at h2
  change ‖(WithLp.toLp 2 (Sum.elim (0 : R → ℂ) (B *ᵥ x)) : EuclideanSpace ℂ (R ⊕ C))‖^2 ≤
    ‖Matrix.fromBlocks A 0 0 B‖^2 *
      ‖(WithLp.toLp 2 (Sum.elim (0 : R → ℂ) x) : EuclideanSpace ℂ (R ⊕ C))‖^2 at h2
  rw [euclidean_sum_elim_norm_sq, euclidean_sum_elim_norm_sq] at h2
  simpa using h2

/-- Exact L2 operator norm of a block diagonal matrix, including either empty summand. -/
theorem matrix_l2_blockDiagonal_norm (A : Matrix R R ℂ) (B : Matrix C C ℂ) :
    ‖Matrix.fromBlocks A 0 0 B‖ = max ‖A‖ ‖B‖ :=
  le_antisymm (matrix_l2_blockDiagonal_norm_le A B)
    (max_le (matrix_l2_left_norm_le_blockDiagonal A B) (matrix_l2_right_norm_le_blockDiagonal A B))

end CertificationGaussian
