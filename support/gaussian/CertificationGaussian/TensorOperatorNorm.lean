import CertificationGaussian.MatrixKroneckerNorm
import CertificationGaussian.ComplexGaussianMatrixWick
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- Coordinate relabelling is an isometry for the genuine Euclidean operator norm. -/
theorem matrix_l2_opNorm_submatrix_equiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (A : Matrix J J ℂ) :
    ‖A.submatrix e e‖=‖A‖ := by
  let f : Matrix J J ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ :=
    { Matrix.reindexAlgEquiv ℂ ℂ e.symm with
      map_smul' := by intro c M; rfl
      map_star' := by intro M; rfl }
  exact StarAlgEquiv.norm_map f A

/-- Exact finite tensor norm, including the empty tensor and empty local index types. -/
theorem wickTensorMatrix_fin_norm {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (A : Fin n → Matrix I I ℂ) :
    ‖wickTensorMatrix A‖ = ∏ a, ‖A a‖ := by
  induction n with
  | zero =>
    have he : wickTensorMatrix A = (1 : Matrix (Fin 0 → I) (Fin 0 → I) ℂ) := by
      ext x y
      have hxy : x=y := Subsingleton.elim _ _
      simp [wickTensorMatrix,Matrix.one_apply,hxy]
    rw [he]
    simp
  | succ n ih =>
    let e : (Fin (n+1) → I) ≃ I × (Fin n → I) := (Fin.consEquiv (fun _ => I)).symm
    have he : wickTensorMatrix A =
        (Matrix.kronecker (A 0) (wickTensorMatrix (fun a => A a.succ))).submatrix e e := by
      ext x y
      simp only [wickTensorMatrix,Matrix.submatrix_apply,
        Fin.prod_univ_succ]
      rfl
    rw [he,matrix_l2_opNorm_submatrix_equiv,matrix_l2_opNorm_kronecker,ih,
      Fin.prod_univ_succ]

/-- Exact operator norm of the existing actual coordinate tensor. -/
theorem wickTensorMatrix_norm {T I : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] (A : T → Matrix I I ℂ) :
    ‖wickTensorMatrix A‖ = ∏ a, ‖A a‖ := by
  let e := Fintype.equivFin T
  let f : (T → I) ≃ (Fin (Fintype.card T) → I) :=
    Equiv.piCongrLeft' (fun _ => I) e
  have he : wickTensorMatrix A =
      (wickTensorMatrix (fun a => A (e.symm a))).submatrix f f := by
    ext x y
    exact (e.symm.prod_comp (fun a => A a (x a) (y a))).symm
  rw [he,matrix_l2_opNorm_submatrix_equiv,wickTensorMatrix_fin_norm]
  exact e.symm.prod_comp (fun a => ‖A a‖)

end CertificationGaussian
