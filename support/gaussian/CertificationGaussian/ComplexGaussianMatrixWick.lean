import CertificationGaussian.FiniteWickInclusionExclusionFourBlock
import CertificationGaussian.ComplexGaussianFourBlockWick
import Mathlib.LinearAlgebra.Matrix.Permutation

noncomputable section
open MeasureTheory MvPolynomial Finset Matrix
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Enumerating a pair by its two positions, without requiring distinct values. -/
theorem sum_finTwo_function {R : Type*} [AddCommMonoid R] (f : (Fin 2 → I) → R) :
    (∑ x, f x) = ∑ a, ∑ b, f ![a,b] := by
  rw [← (finTwoArrowEquiv I).symm.sum_comp f,Fintype.sum_prod_type]
  rfl

omit [DecidableEq I] in
/-- The local matrix contraction is a sum over two bar and two unbar position labels. -/
theorem gaussianNormalMatrixPolynomial_as_positions (A : Fin 2 → Matrix I I ℂ) :
    gaussianNormalMatrixPolynomial (A 0) (A 1) =
      ∑ i : Fin 2 → I, ∑ j : Fin 2 → I,
        C (∏ a : Fin 2, A a (i a) (j a)) * gaussianNormalQuartic (i 0) (i 1) (j 0) (j 1) := by
  rw [sum_finTwo_function]
  simp_rw [sum_finTwo_function]
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

omit [DecidableEq I] in
/-- Product of the four actual matrix normal polynomials expanded over all eight positions. -/
theorem gaussianNormalMatrixPolynomial_prod_positions (A : Fin 4 × Fin 2 → Matrix I I ℂ) :
    (∏ b : Fin 4, gaussianNormalMatrixPolynomial (A (b,0)) (A (b,1))) =
      ∑ i : (Fin 4 × Fin 2 → I), ∑ j : (Fin 4 × Fin 2 → I),
        C (∏ a, A a (i a) (j a)) *
          ∏ b : Fin 4, gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1)) := by
  have hb (b : Fin 4) := gaussianNormalMatrixPolynomial_as_positions (fun a => A (b,a))
  simp_rw [hb,Fintype.prod_sum]
  have hc (f : (Fin 4 × Fin 2 → I) → MvPolynomial (Fin 2 × I) ℂ) :
      (∑ x, f x) = ∑ x : Fin 4 → Fin 2 → I, f (fun a => x a.1 a.2) := by
    exact ((Equiv.curry (Fin 4) (Fin 2) I).symm.sum_comp f).symm
  rw [hc]
  simp_rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.prod_mul_distrib,← map_prod,Fintype.prod_prod_type]

omit [Fintype I] in
/-- Multiplying coordinate deltas is the delta on the entire labelled function. -/
theorem prod_coordinate_delta {T : Type*} [Fintype T] (f g : T → I) :
    (∏ a, if f a=g a then (1:ℂ) else 0) = if f=g then 1 else 0 := by
  classical
  by_cases h : f=g
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨a,ha⟩ : ∃ a, f a ≠ g a := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [ha]

/-- A fixed pairing contracts the right indices by the inverse permutation. -/
theorem matrix_wick_delta_contraction {T : Type*} [Fintype T] [DecidableEq T]
    (A : T → Matrix I I ℂ) (π : Equiv.Perm T) (i : T → I) :
    (∑ j : T → I, (∏ a, A a (i a) (j a)) *
      ∏ a, if i a=j (π a) then (1:ℂ) else 0) =
      ∏ a, A a (i a) (i (π.symm a)) := by
  have hd (j : T → I) : (∏ a, if i a=j (π a) then (1:ℂ) else 0) =
      if (fun a => i (π.symm a))=j then 1 else 0 := by
    rw [← π.symm.prod_comp (fun a => if i a=j (π a) then (1:ℂ) else 0)]
    simp only [Equiv.apply_symm_apply]
    exact prod_coordinate_delta _ _
  simp_rw [hd]
  simp [mul_ite]

/-- Complete finite matrix-entry version of the four-block Wick identity. -/
theorem complexGaussian_four_matrix_blocks_entries (A : Fin 4 × Fin 2 → Matrix I I ℂ) :
    complexGaussianPolyExpectation (∏ b : Fin 4, gaussianNormalMatrixPolynomial (A (b,0)) (A (b,1))) =
      ∑ π ∈ fourBlockDerangements, ∑ i : Fin 4 × Fin 2 → I,
        ∏ a, A a (i a) (i (π.symm a)) := by
  rw [gaussianNormalMatrixPolynomial_prod_positions]
  simp only [complexGaussianPolyExpectation_sum,complexGaussianPolyExpectation_C_mul,
    complexGaussian_four_normal_blocks_finite_inclusion_exclusion,Finset.mul_sum]
  simp only [Finset.sum_comm (s := Finset.univ) (t := fourBlockDerangements)]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro i _
  exact matrix_wick_delta_contraction A π i

/-- The actual tensor-product matrix on the labelled coordinate functions. -/
def wickTensorMatrix {T : Type*} [Fintype T] (A : T → Matrix I I ℂ) :
    Matrix (T → I) (T → I) ℂ := fun x y => ∏ a, A a (x a) (y a)

/-- Relabelling tensor slots by π; the inverse is explicit. -/
def wickTensorCoordinatePermutation {T : Type*} (π : Equiv.Perm T) : Equiv.Perm (T → I) where
  toFun x a := x (π a)
  invFun x a := x (π.symm a)
  left_inv x := by funext a; simp
  right_inv x := by funext a; simp

/-- A genuine permutation matrix on the tensor coordinates, fixing the trace convention. -/
def wickTensorPermutationMatrix {T : Type*} [Fintype T] (π : Equiv.Perm T) :
    Matrix (T → I) (T → I) ℂ := (wickTensorCoordinatePermutation (I := I) π).permMatrix ℂ

/-- Exact trace contraction for the convention used here, with π-inverse on the column labels. -/
theorem wickTensorMatrix_permutation_trace {T : Type*} [Fintype T] [DecidableEq T]
    (A : T → Matrix I I ℂ) (π : Equiv.Perm T) :
    Matrix.trace (wickTensorMatrix A * wickTensorPermutationMatrix π) =
      ∑ i : T → I, ∏ a, A a (i a) (i (π.symm a)) := by
  simp [wickTensorMatrix,wickTensorPermutationMatrix,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Equiv.Perm.permMatrix,wickTensorCoordinatePermutation]
  have he (i j : T → I) : (fun a => j (π a))=i ↔ j=(fun a => i (π.symm a)) := by
    constructor
    · intro h
      funext a
      simpa using congrFun h (π.symm a)
    · intro h
      subst j
      funext a
      simp
  simp [he]

/-- The tensor-coordinate matrix is genuinely unitary, including an empty coordinate space. -/
theorem wickTensorPermutationMatrix_unitary {T : Type*} [Fintype T] [DecidableEq T] (π : Equiv.Perm T) :
    wickTensorPermutationMatrix (I := I) π ∈ unitary (Matrix (T → I) (T → I) ℂ) := by
  constructor <;>
    simp only [wickTensorPermutationMatrix,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul,inv_mul_cancel,mul_inv_cancel,Matrix.permMatrix_one]

/-- Exclusion of all within-block edges is stable under inversion. -/
theorem fourBlockDerangements_inv (π : Equiv.Perm (Fin 4 × Fin 2)) :
    π ∈ fourBlockDerangements ↔ π.symm ∈ fourBlockDerangements := by
  simp only [fourBlockDerangements,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h a
    exact Ne.symm (by simpa using h (π.symm a))
  · intro h a
    exact Ne.symm (by simpa using h (π a))

/-- The actual product of all four W polynomials is integrable under the true complex Gaussian law. -/
theorem complexGaussian_four_matrix_blocks_integrable (A : Fin 4 × Fin 2 → Matrix I I ℂ) :
    Integrable (fun x => ∏ b : Fin 4,
      complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x)) (pairedGaussian I) := by
  have he : (fun x => ∏ b : Fin 4, complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x)) =
      complexCoordinatePolyEval (∏ b : Fin 4, gaussianNormalMatrixPolynomial (A (b,0)) (A (b,1))) := by
    funext x
    simp only [complexCoordinatePolyEval,map_prod,
      show ∀ b : Fin 4, eval (fun c => (x c:ℂ)) (gaussianNormalMatrixPolynomial (A (b,0)) (A (b,1))) =
        complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x) from
        fun b => gaussianNormalMatrixPolynomial_eval _ _ x]
  rw [he]
  exact complexCoordinatePolyEval_integrable _

/-- The normal-order Wick identity for four arbitrary complex matrix blocks.
The right side uses actual tensor and unitary permutation matrices, not a trace symbol defined as the sum. -/
theorem complexGaussian_four_matrix_blocks_trace (A : Fin 4 × Fin 2 → Matrix I I ℂ) :
    (∫ x, ∏ b : Fin 4, complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x)
      ∂pairedGaussian I) =
      ∑ π ∈ fourBlockDerangements, Matrix.trace (wickTensorMatrix A * wickTensorPermutationMatrix π) := by
  have h := complexGaussian_four_matrix_blocks_entries A
  simpa only [complexGaussianPolyExpectation,complexCoordinatePolyEval,map_prod,
    show ∀ x b, eval (fun c => (x c:ℂ)) (gaussianNormalMatrixPolynomial (A (b,0)) (A (b,1))) =
      complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x) from
      fun x b => gaussianNormalMatrixPolynomial_eval _ _ x,
    wickTensorMatrix_permutation_trace] using h

end CertificationGaussian
