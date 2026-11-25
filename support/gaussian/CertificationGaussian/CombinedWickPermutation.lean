import CertificationGaussian.UnchangedSiteContraction
import CertificationGaussian.PauliChangedSiteTensor

noncomputable section
open Matrix
open scoped BigOperators
namespace CertificationGaussian

/-- Separate the two input slots and the output slot of each of the four blocks. -/
def tripleBlockCoordinates (I : Type*) :
    (Fin 4 → ((I × I) × I)) ≃ ((Fin 4 × Fin 2 → I) × (Fin 4 → I)) where
  toFun x := (fun t => if t.2=0 then (x t.1).1.1 else (x t.1).1.2,fun b => (x b).2)
  invFun y b := ((y.1 (b,0),y.1 (b,1)),y.2 b)
  left_inv x := by
    funext b
    simp
  right_inv y := by
    apply Prod.ext
    · funext ⟨b,s⟩
      fin_cases s <;> rfl
    · rfl

/-- The inverse of this permutation advances once around the output trace cycle. -/
def outputTraceCycle : Equiv.Perm (Fin 4) where
  toFun i := ![3,0,1,2] i
  invFun i := ![1,2,3,0] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- A genuine permutation on the twelve grouped tensor slots: Wick on eight inputs and a cycle on four outputs. -/
def combinedWickCoordinatePermutation {I : Type*} (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Equiv.Perm (Fin 4 → ((I × I) × I)) :=
  (tripleBlockCoordinates I).trans
    ((Equiv.prodCongr (wickTensorCoordinatePermutation (I := I) π)
      (wickTensorCoordinatePermutation (I := I) outputTraceCycle)).trans
        (tripleBlockCoordinates I).symm)

variable {I : Type*} [Fintype I] [DecidableEq I]

def combinedWickPermutationMatrix (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Matrix (Fin 4 → ((I × I) × I)) (Fin 4 → ((I × I) × I)) ℂ :=
  (combinedWickCoordinatePermutation (I := I) π).permMatrix ℂ

theorem combinedWickPermutationMatrix_unitary (π : Equiv.Perm (Fin 4 × Fin 2)) :
    combinedWickPermutationMatrix (I := I) π∈unitary _ := by
  constructor <;>
    simp only [combinedWickPermutationMatrix,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix,← Matrix.permMatrix_mul,inv_mul_cancel,mul_inv_cancel,
      Matrix.permMatrix_one]

omit [Fintype I] [DecidableEq I] in
theorem combinedWickCoordinatePermutation_symm_apply (π : Equiv.Perm (Fin 4 × Fin 2))
    (x : Fin 4 → ((I × I) × I)) (b : Fin 4) :
    (combinedWickCoordinatePermutation π).symm x b =
      (((tripleBlockCoordinates I x).1 (π.symm (b,0)),
        (tripleBlockCoordinates I x).1 (π.symm (b,1))),
        (tripleBlockCoordinates I x).2 (outputTraceCycle.symm b)) := rfl

/-- The actual trace of the grouped four-block tensor against this unitary permutation. -/
theorem combinedWickPermutationMatrix_trace (K : Fin 4 → Matrix ((I × I) × I) ((I × I) × I) ℂ)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Matrix.trace (wickTensorMatrix K*combinedWickPermutationMatrix π) =
      ∑ x : Fin 4 → ((I × I) × I),∏ b,K b (x b) ((combinedWickCoordinatePermutation π).symm x b) := by
  have he (x y : Fin 4 → ((I × I) × I)) :
      combinedWickCoordinatePermutation π y=x ↔ y=(combinedWickCoordinatePermutation π).symm x :=
    (Equiv.eq_symm_apply (combinedWickCoordinatePermutation π)).symm
  simp [combinedWickPermutationMatrix,wickTensorMatrix,Matrix.trace,Matrix.diag,
    Matrix.mul_apply,Equiv.Perm.permMatrix,he]

/-- The grouped input/output tensor contraction factors into the actual two tensor traces. -/
theorem combinedWickPermutationMatrix_tensor_trace
    (A : Fin 4 × Fin 2 → Matrix I I ℂ) (P : Fin 4 → Matrix I I ℂ)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Matrix.trace (wickTensorMatrix (fun b =>
      Matrix.kronecker (Matrix.kronecker (A (b,0)) (A (b,1))) (P b))*combinedWickPermutationMatrix π) =
      Matrix.trace (wickTensorMatrix A*wickTensorPermutationMatrix π)*
        Matrix.trace (wickTensorMatrix P*wickTensorPermutationMatrix outputTraceCycle) := by
  rw [combinedWickPermutationMatrix_trace,wickTensorMatrix_permutation_trace,
    wickTensorMatrix_permutation_trace]
  have he (x : Fin 4 → ((I × I) × I)) :
      (∏ b,Matrix.kronecker (Matrix.kronecker (A (b,0)) (A (b,1))) (P b)
        (x b) ((combinedWickCoordinatePermutation π).symm x b)) =
      (∏ t : Fin 4 × Fin 2,A t ((tripleBlockCoordinates I x).1 t)
        ((tripleBlockCoordinates I x).1 (π.symm t))) *
      (∏ b : Fin 4,P b ((tripleBlockCoordinates I x).2 b)
        ((tripleBlockCoordinates I x).2 (outputTraceCycle.symm b))) := by
    simp only [combinedWickCoordinatePermutation_symm_apply]
    change (∏ b,A (b,0) (x b).1.1 ((tripleBlockCoordinates I x).1 (π.symm (b,0))) *
      A (b,1) (x b).1.2 ((tripleBlockCoordinates I x).1 (π.symm (b,1))) *
      P b (x b).2 ((tripleBlockCoordinates I x).2 (outputTraceCycle.symm b))) = _
    rw [Fintype.prod_prod_type]
    simp only [Fin.prod_univ_two,Finset.prod_mul_distrib]
    congr 2
  simp_rw [he]
  rw [← Equiv.sum_comp (tripleBlockCoordinates I).symm
    (fun x => (∏ t : Fin 4 × Fin 2,A t ((tripleBlockCoordinates I x).1 t)
      ((tripleBlockCoordinates I x).1 (π.symm t))) *
      ∏ b : Fin 4,P b ((tripleBlockCoordinates I x).2 b)
        ((tripleBlockCoordinates I x).2 (outputTraceCycle.symm b)))]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- Coordinate enumeration follows the order of the three matrix products in the output trace. -/
def fourMatrixTraceCoordinates (I : Type*) : (Fin 4 → I) ≃ (I × (I × (I × I))) where
  toFun x := (x 0,x 3,x 2,x 1)
  invFun x := ![x.1,x.2.2.2,x.2.2.1,x.2.1]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := rfl

/-- The output tensor cycle is precisely the original four-matrix product, with its complex phase. -/
theorem outputTraceCycle_trace (P : Fin 4 → Matrix I I ℂ) :
    Matrix.trace (wickTensorMatrix P*wickTensorPermutationMatrix outputTraceCycle) =
      Matrix.trace (P 0*P 1*P 2*P 3) := by
  rw [wickTensorMatrix_permutation_trace]
  rw [← Equiv.sum_comp (fourMatrixTraceCoordinates I).symm
    (fun x => ∏ b,P b (x b) (x (outputTraceCycle.symm b)))]
  have he (x : I × (I × (I × I))) :
      (∏ b,P b ((fourMatrixTraceCoordinates I).symm x b)
        ((fourMatrixTraceCoordinates I).symm x (outputTraceCycle.symm b))) =
      P 0 x.1 x.2.2.2*P 1 x.2.2.2 x.2.2.1*P 2 x.2.2.1 x.2.1*P 3 x.2.1 x.1 := by
    change (∏ b,P b (![x.1,x.2.2.2,x.2.2.1,x.2.1] b)
      (![x.1,x.2.2.2,x.2.2.1,x.2.1] (outputTraceCycle.symm b))) = _
    simp [outputTraceCycle,Fin.prod_univ_succ,mul_assoc]
  simp_rw [he]
  simp only [Fintype.sum_prod_type,Matrix.trace,Matrix.diag,Matrix.mul_apply,Finset.sum_mul]

/-- The full grouped tensor/permutation contraction is exactly input Wick trace times output trace. -/
theorem combinedWickPermutationMatrix_actual_trace
    (A : Fin 4 × Fin 2 → Matrix I I ℂ) (P : Fin 4 → Matrix I I ℂ)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Matrix.trace (wickTensorMatrix (fun b =>
      Matrix.kronecker (Matrix.kronecker (A (b,0)) (A (b,1))) (P b))*combinedWickPermutationMatrix π) =
      Matrix.trace (P 0*P 1*P 2*P 3)*
        Matrix.trace (wickTensorMatrix A*wickTensorPermutationMatrix π) := by
  rw [combinedWickPermutationMatrix_tensor_trace,outputTraceCycle_trace,mul_comm]

end CertificationGaussian
