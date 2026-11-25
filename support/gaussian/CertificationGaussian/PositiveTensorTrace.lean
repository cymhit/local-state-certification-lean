import CertificationGaussian.HermitianTraceBound
import CertificationGaussian.ComplexGaussianMatrixWick
import Mathlib.Analysis.Matrix.Order

noncomputable section
open Matrix Unitary Finset
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
namespace CertificationGaussian
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A full complex diagonal spectral coefficient is controlled by the actual Euclidean operator norm. -/
theorem spectral_conjugate_diagonal_norm_le (X V : Matrix N N ℂ) (hX : X.IsHermitian) (i : N) :
    ‖(conjStarAlgAut ℂ (Matrix N N ℂ) (star hX.eigenvectorUnitary) V) i i‖ ≤
      ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V‖ := by
  rw [spectral_conjugate_diagonal]
  have hn : ‖hX.eigenvectorBasis i‖=1 := hX.eigenvectorBasis.orthonormal.norm_eq_one i
  calc
    ‖inner ℂ (hX.eigenvectorBasis i) (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V (hX.eigenvectorBasis i))‖ ≤
      ‖hX.eigenvectorBasis i‖ * ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V (hX.eigenvectorBasis i)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖hX.eigenvectorBasis i‖ *
        (‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V‖ * ‖hX.eigenvectorBasis i‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V).le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [hn]; ring

/-- Positivity of the first matrix controls the modulus of its trace pairing with an arbitrary operator. -/
theorem posSemidef_trace_mul_norm_le (A V : Matrix N N ℂ) (hA : A.PosSemidef) :
    ‖Matrix.trace (A*V)‖ ≤ ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V‖*(Matrix.trace A).re := by
  rw [Matrix.trace_mul_comm]
  have he := trace_mul_hermitian_power A V hA.isHermitian 1
  simp only [pow_one] at he
  rw [he,hA.isHermitian.trace_eq_sum_eigenvalues]
  calc
    ‖∑ i, (conjStarAlgAut ℂ (Matrix N N ℂ) (star hA.isHermitian.eigenvectorUnitary) V) i i *
      (hA.isHermitian.eigenvalues i : ℂ)‖ ≤
        ∑ i, ‖(conjStarAlgAut ℂ (Matrix N N ℂ) (star hA.isHermitian.eigenvectorUnitary) V) i i *
          (hA.isHermitian.eigenvalues i : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, ‖(conjStarAlgAut ℂ (Matrix N N ℂ) (star hA.isHermitian.eigenvectorUnitary) V) i i‖ *
        hA.isHermitian.eigenvalues i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hA.eigenvalues_nonneg i)]
    _ ≤ ∑ i, ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) V‖ * hA.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (spectral_conjugate_diagonal_norm_le A V hA.isHermitian i)
        (hA.eigenvalues_nonneg i)
    _ = _ := by simp [Complex.re_sum,Finset.mul_sum]

/-- Unitaries have operator norm at most one even in zero dimension. -/
theorem unitary_matrix_norm_le_one (U : Matrix N N ℂ) (hU : U ∈ unitary (Matrix N N ℂ)) :
    ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) U‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  rcases isEmpty_or_nonempty N with h | h
  · let := h
    have he : U=0 := Subsingleton.elim _ _
    simp [he]
  · let := h
    exact (CStarRing.norm_of_mem_unitary hU).le

/-- The changed-site contraction estimate uses a genuine unitary matrix and the actual PSD trace. -/
theorem posSemidef_trace_unitary_le (A U : Matrix N N ℂ) (hA : A.PosSemidef)
    (hU : U ∈ unitary (Matrix N N ℂ)) : ‖Matrix.trace (A*U)‖ ≤ (Matrix.trace A).re := by
  have ht : 0 ≤ (Matrix.trace A).re := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  calc
    ‖Matrix.trace (A*U)‖ ≤ ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) U‖*(Matrix.trace A).re :=
      posSemidef_trace_mul_norm_le A U hA
    _ ≤ 1*(Matrix.trace A).re := mul_le_mul_of_nonneg_right (unitary_matrix_norm_le_one U hU) ht
    _ = _ := one_mul _

/-- The actual tensor matrix has the product of the individual traces. -/
theorem wickTensorMatrix_trace {T I : Type*} [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I]
    (A : T → Matrix I I ℂ) : Matrix.trace (wickTensorMatrix A) = ∏ a, Matrix.trace (A a) := by
  simp only [Matrix.trace,Matrix.diag,wickTensorMatrix]
  exact (Fintype.prod_sum (fun a i => A a i i)).symm

/-- Positivity of the actual coordinate tensor, proved by Kronecker positivity and reindexing. -/
theorem wickTensorMatrix_fin_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (A : Fin n → Matrix I I ℂ) (hA : ∀ a, (A a).PosSemidef) :
    (wickTensorMatrix A).PosSemidef := by
  induction n with
  | zero =>
    have he : wickTensorMatrix A = (1 : Matrix (Fin 0 → I) (Fin 0 → I) ℂ) := by
      ext x y
      have hxy : x=y := Subsingleton.elim _ _
      simp [wickTensorMatrix,Matrix.one_apply,hxy]
    rw [he]
    exact Matrix.PosSemidef.one
  | succ n ih =>
    have hp := (hA 0).kronecker (ih (fun a => A a.succ) (fun a => hA a.succ))
    have hs := hp.submatrix (fun x : Fin (n+1) → I => (x 0,fun a : Fin n => x a.succ))
    convert hs using 1
    ext x y
    simp only [wickTensorMatrix,Matrix.submatrix_apply,Matrix.kronecker_apply,Fin.prod_univ_succ]

/-- Arbitrary finite tensor labels, matching the Wick permutation matrix index space. -/
theorem wickTensorMatrix_posSemidef {T I : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] (A : T → Matrix I I ℂ) (hA : ∀ a, (A a).PosSemidef) :
    (wickTensorMatrix A).PosSemidef := by
  let e := Fintype.equivFin T
  have hp := wickTensorMatrix_fin_posSemidef (Fintype.card T) (fun a => A (e.symm a))
    (fun a => hA (e.symm a))
  have hs := hp.submatrix (fun x : T → I => fun a => x (e.symm a))
  convert hs using 1
  ext x y
  exact (e.symm.prod_comp (fun a => A a (x a) (y a))).symm

/-- PSD traces are real, so the real tensor trace is the product of the real traces. -/
theorem wickTensorMatrix_trace_re {T I : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] (A : T → Matrix I I ℂ) (hA : ∀ a, (A a).PosSemidef) :
    (Matrix.trace (wickTensorMatrix A)).re = ∏ a, (Matrix.trace (A a)).re := by
  rw [wickTensorMatrix_trace]
  have hr (a : T) : Matrix.trace (A a)=((Matrix.trace (A a)).re : ℂ) := by
    have hi : (Matrix.trace (A a)).im=0 := (RCLike.nonneg_iff.mp (hA a).trace_nonneg).2
    exact Complex.ext rfl (by simpa using hi)
  have he : (∏ a, Matrix.trace (A a)) = ((∏ a, (Matrix.trace (A a)).re : ℝ) : ℂ) := by
    calc
      (∏ a, Matrix.trace (A a)) = ∏ a, ((Matrix.trace (A a)).re : ℂ) :=
        Finset.prod_congr rfl (fun a _ => hr a)
      _ = _ := (map_prod (algebraMap ℝ ℂ) (fun a => (Matrix.trace (A a)).re) Finset.univ).symm
  rw [he]
  rfl

/-- Every true tensor permutation contraction of positive factors is bounded by their product trace. -/
theorem wickTensorMatrix_permutation_trace_norm_le {T I : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] (A : T → Matrix I I ℂ) (hA : ∀ a, (A a).PosSemidef)
    (π : Equiv.Perm T) :
    ‖Matrix.trace (wickTensorMatrix A * wickTensorPermutationMatrix π)‖ ≤
      ∏ a, (Matrix.trace (A a)).re := by
  rw [← wickTensorMatrix_trace_re A hA]
  exact posSemidef_trace_unitary_le _ _ (wickTensorMatrix_posSemidef A hA)
    (wickTensorPermutationMatrix_unitary π)

/-- A common local trace bound gives the dimension-free finite tensor estimate. -/
theorem wickTensorMatrix_permutation_trace_uniform {T I : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] (A : T → Matrix I I ℂ) (hA : ∀ a, (A a).PosSemidef)
    (τ : ℝ) (hτ : ∀ a, (Matrix.trace (A a)).re ≤ τ) (π : Equiv.Perm T) :
    ‖Matrix.trace (wickTensorMatrix A * wickTensorPermutationMatrix π)‖ ≤ τ^(Fintype.card T) := by
  calc
    ‖Matrix.trace (wickTensorMatrix A * wickTensorPermutationMatrix π)‖ ≤ ∏ a, (Matrix.trace (A a)).re :=
      wickTensorMatrix_permutation_trace_norm_le A hA π
    _ ≤ ∏ _a : T, τ := Finset.prod_le_prod₀
      (fun a _ => (RCLike.nonneg_iff.mp (hA a).trace_nonneg).1) (fun a _ => hτ a)
    _ = _ := by simp

end CertificationGaussian
