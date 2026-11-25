import CertificationGaussian.TensorUnitaryNet
import CertificationGaussian.UnitaryFrobeniusPacking
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.CStarAlgebra.Spectrum

noncomputable section
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Classical
namespace CertificationGaussian
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Amplifying a matrix by the identity is a star-algebra homomorphism. -/
def matrixKroneckerLeftHom : Matrix I I ℂ →⋆ₙₐ[ℂ] Matrix (I × J) (I × J) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix J J ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  map_mul' A B := by simpa using Matrix.mul_kronecker_mul A B (1 : Matrix J J ℂ) 1
  map_smul' c A := Matrix.smul_kronecker c A _
  map_star' A := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

def matrixKroneckerRightHom : Matrix J J ℂ →⋆ₙₐ[ℂ] Matrix (I × J) (I × J) ℂ where
  toFun B := (1 : Matrix I I ℂ) ⊗ₖ B
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ A B
  map_mul' A B := by simpa using Matrix.mul_kronecker_mul (1 : Matrix I I ℂ) 1 A B
  map_smul' c A := Matrix.kronecker_smul c _ A
  map_star' A := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

/-- Contractivity of the two amplifications gives the dimension-free tensor bound. -/
theorem matrix_kronecker_operator_norm_le_of_star_hom (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  have he : A ⊗ₖ B = matrixKroneckerLeftHom (J := J) A * matrixKroneckerRightHom (I := I) B := by
    change A ⊗ₖ B = (A ⊗ₖ 1) * (1 ⊗ₖ B)
    rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
  rw [he]
  exact (norm_mul_le _ _).trans (mul_le_mul
    (NonUnitalStarAlgHom.norm_apply_le (matrixKroneckerLeftHom (J := J)) A)
    (NonUnitalStarAlgHom.norm_apply_le (matrixKroneckerRightHom (I := I)) B)
    (norm_nonneg _) (norm_nonneg _))

/-- Reindexing changes coordinates, not the Euclidean operator bound. -/
def matrixReindexStarAlgEquiv (e : I ≃ J) : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := fun c A => rfl
    map_star' := fun A => by
      change Matrix.reindex e e A.conjTranspose = (Matrix.reindex e e A).conjTranspose
      exact (Matrix.conjTranspose_reindex e e A).symm }

theorem matrix_reindex_operator_norm_le_of_star_equiv (e : I ≃ J) (A : Matrix I I ℂ) :
    ‖Matrix.reindex e e A‖ ≤ ‖A‖ :=
  NonUnitalStarAlgHom.norm_apply_le (matrixReindexStarAlgEquiv e) A

/-- Empty index types are included; on a nonempty index the unitary norm is exactly one. -/
theorem matrix_unitary_operator_norm_le_one (A : Matrix I I ℂ)
    (hA : A ∈ unitary (Matrix I I ℂ)) : ‖A‖ ≤ 1 := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    have : A = 0 := Subsingleton.elim _ _
    simp [this]
  | inr h => exact (CStarRing.norm_of_mem_unitary hA).le

/-- The recursive tensor formula is the actual entrywise product matrix under `Fin.cons`. -/
theorem tensorUnitaryMatrix_succ_kronecker {d n : Nat} (U : Fin (n+1) → LocalUnitary d) :
    tensorUnitaryMatrix d (n+1) U =
      Matrix.reindex (Fin.consEquiv (fun _ : Fin (n+1) => Fin d))
        (Fin.consEquiv (fun _ : Fin (n+1) => Fin d))
        ((U 0).1 ⊗ₖ tensorUnitaryMatrix d n (fun i => U i.succ)) := by
  ext x y
  simp [tensorUnitaryMatrix, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.submatrix_apply, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]

/-- Site telescoping in operator norm: all untouched unitary tensor factors have norm at most one. -/
theorem tensorUnitaryMatrix_operator_close_of_local_operator {d n : Nat}
    (U V : Fin n → LocalUnitary d) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ k, ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) ((U k).1-(V k).1)‖ ≤ ε) :
    ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ)
      (tensorUnitaryMatrix d n U-tensorUnitaryMatrix d n V)‖ ≤ n*ε := by
  simp only [Matrix.l2_opNorm_toEuclideanCLM] at hclose ⊢
  induction n with
  | zero =>
    have he : tensorUnitaryMatrix d 0 U = tensorUnitaryMatrix d 0 V := by
      ext x y
      simp [tensorUnitaryMatrix]
    simp [he]
  | succ n ih =>
    let A := tensorUnitaryMatrix d n (fun i => U i.succ)
    let B := tensorUnitaryMatrix d n (fun i => V i.succ)
    have hA : ‖A‖ ≤ 1 := matrix_unitary_operator_norm_le_one A (tensorUnitaryMatrix_unitary _ _ _)
    have hV : ‖(V 0).1‖ ≤ 1 := matrix_unitary_operator_norm_le_one _ (V 0).2
    have hab : ‖A-B‖ ≤ n*ε := ih (fun i => U i.succ) (fun i => V i.succ) (fun i => hclose i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin d)
    have he : tensorUnitaryMatrix d (n+1) U-tensorUnitaryMatrix d (n+1) V =
        Matrix.reindex e e (((U 0).1-(V 0).1) ⊗ₖ A + (V 0).1 ⊗ₖ (A-B)) := by
      rw [tensorUnitaryMatrix_succ_kronecker U, tensorUnitaryMatrix_succ_kronecker V]
      change Matrix.reindex e e ((U 0).1 ⊗ₖ A) - Matrix.reindex e e ((V 0).1 ⊗ₖ B) = _
      ext x y
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.kroneckerMap_apply]
      ring
    rw [he]
    calc
      _ ≤ ‖((U 0).1-(V 0).1) ⊗ₖ A + (V 0).1 ⊗ₖ (A-B)‖ := matrix_reindex_operator_norm_le_of_star_equiv _ _
      _ ≤ ‖((U 0).1-(V 0).1) ⊗ₖ A‖ + ‖(V 0).1 ⊗ₖ (A-B)‖ := norm_add_le _ _
      _ ≤ ‖(U 0).1-(V 0).1‖*‖A‖ + ‖(V 0).1‖*‖A-B‖ :=
        add_le_add (matrix_kronecker_operator_norm_le_of_star_hom _ _) (matrix_kronecker_operator_norm_le_of_star_hom _ _)
      _ ≤ ε*1 + 1*(n*ε) := add_le_add
        (mul_le_mul (hclose 0) hA (norm_nonneg _) hε)
        (mul_le_mul hV hab (norm_nonneg _) (by norm_num))
      _ = (n+1:Nat)*ε := by push_cast; ring

/-- Local Frobenius errors give the paper's `n ε`, with no ambient dimension multiplier. -/
theorem tensorUnitaryMatrix_operator_close_of_local_frobenius {d n : Nat} (U V : Fin n → LocalUnitary d)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ k, (∑ i, ∑ j, ‖(U k).1 i j-(V k).1 i j‖^2) ≤ ε^2) :
    ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ)
      (tensorUnitaryMatrix d n U-tensorUnitaryMatrix d n V)‖ ≤ n*ε := by
  apply tensorUnitaryMatrix_operator_close_of_local_operator U V hε
  intro k
  apply (matrix_operator_norm_le_entry_sqrt _).trans
  exact (Real.sqrt_le_sqrt (hclose k)).trans_eq (Real.sqrt_sq hε)

/-- Independently choose a Frobenius packing-net unitary at each site. -/
def productPackingTupleNet (d n : Nat) (ε : ℝ) (hε : 0 < ε) :
    Finset (Fin n → LocalUnitary d) :=
  Fintype.piFinset (fun _ => unitaryPackingNet d ε hε)

/-- The net consists of actual tensor-product basis matrices. -/
def productPackingMatrixNet (d n : Nat) (ε : ℝ) (hε : 0 < ε) :
    Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :=
  (productPackingTupleNet d n ε hε).image (tensorUnitaryMatrix d n)

theorem productPackingMatrixNet_unitary {d n : Nat} {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (QuditIndex d n) (QuditIndex d n) ℂ}
    (hW : W ∈ productPackingMatrixNet d n ε hε) :
    W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) := by
  obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hW
  exact tensorUnitaryMatrix_unitary d n V

theorem productPackingMatrixNet_covers {d n : Nat} {ε : ℝ} (hε : 0 < ε)
    (U : Fin n → LocalUnitary d) :
    ∃ W ∈ productPackingMatrixNet d n ε hε,
      ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ)
        (tensorUnitaryMatrix d n U-W)‖ ≤ n*ε := by
  choose V hm hc using fun k => unitaryPackingNet_covers_sq hε (U k)
  refine ⟨tensorUnitaryMatrix d n V, Finset.mem_image.mpr ⟨V, ?_, rfl⟩, ?_⟩
  · exact Fintype.mem_piFinset.mpr hm
  · exact tensorUnitaryMatrix_operator_close_of_local_frobenius U V hε.le hc

theorem productPackingMatrixNet_card {d n : Nat} {ε : ℝ} (hε : 0 < ε) :
    ((productPackingMatrixNet d n ε hε).card:ℝ) ≤
      (1+2*Real.sqrt d/ε)^(2*d^2*n) := by
  have h1 : (productPackingMatrixNet d n ε hε).card ≤ (unitaryPackingNet d ε hε).card^n := by
    apply (Finset.card_image_le).trans
    simp only [productPackingTupleNet, Fintype.card_piFinset_const, le_refl]
  have h1R : ((productPackingMatrixNet d n ε hε).card:ℝ) ≤ ((unitaryPackingNet d ε hε).card^n:Nat) :=
    Nat.cast_le.mpr h1
  rw [Nat.cast_pow] at h1R
  apply h1R.trans
  simpa only [pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) (unitaryPackingNet_card hε) n

end CertificationGaussian
