import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
open Matrix
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Entrywise tensor product on function labels, including an empty set of factors. -/
def tensorMatrix (A : ι → Matrix α α ℂ) : Matrix (ι → α) (ι → α) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

theorem tensorMatrix_mul (A B : ι → Matrix α α ℂ) :
    tensorMatrix (fun i => A i * B i) = tensorMatrix A * tensorMatrix B := by
  classical
  ext x y
  simp only [tensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i z => A i (x i) z * B i z (y i))

omit [Fintype α] [DecidableEq ι] in
theorem tensorMatrix_adjoint (A : ι → Matrix α α ℂ) :
    tensorMatrix (fun i => (A i).conjTranspose) = (tensorMatrix A).conjTranspose := by
  ext x y
  simp [tensorMatrix, Matrix.conjTranspose_apply]

omit [Fintype α] [DecidableEq ι] in
theorem tensorMatrix_one [DecidableEq α] :
    tensorMatrix (fun _ : ι => (1 : Matrix α α ℂ)) = 1 := by
  classical
  ext x y
  simp only [tensorMatrix, Matrix.one_apply, Fintype.prod_ite_zero,
    Finset.prod_const_one, ← funext_iff]

theorem tensorMatrix_trace (A : ι → Matrix α α ℂ) :
    (tensorMatrix A).trace = ∏ i, (A i).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, tensorMatrix]
  exact (Fintype.prod_sum (fun i z => A i z z)).symm

/-- A proved entry contraction determines the action on every matrix, not only product matrices. -/
theorem sum_sandwich_of_entry_contraction {β : Type*} [Fintype β] [DecidableEq α]
    (W V : β → Matrix α α ℂ) (c : ℂ)
    (h : ∀ x y k l, (∑ u, W u x k * V u l y) =
      c * (1 : Matrix α α ℂ) x y * (1 : Matrix α α ℂ) k l)
    (A : Matrix α α ℂ) :
    (∑ u, W u * A * V u) = (c * A.trace) • (1 : Matrix α α ℂ) := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul]
  have he : (∑ u, ∑ l, ∑ k, (W u x k * A k l) * V u l y) =
      ∑ l, ∑ k, (∑ u, W u x k * V u l y) * A k l := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [he]
  simp_rw [h]
  by_cases hxy : x = y
  · subst y
    simp [Matrix.one_apply, Matrix.trace, ← Finset.mul_sum]
  · simp [Matrix.one_apply, hxy]

end LocalCertification.Quantum
