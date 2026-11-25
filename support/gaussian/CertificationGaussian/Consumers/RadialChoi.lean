import CertificationGaussian.RadialChoiTensor

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- Actual finite-site tensor Choi matrices, with signed coefficients and the true Euclidean norm. -/
theorem radial_choi_general (d n r : ℕ) (hd : 0<d) (lam : ℕ → ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      (partialTransposeFirst (radialChoiCombination (S:=Fin n) d r lam))‖ ≤
        ∑ j : Fin (r+1),|lam j.val| * (n.choose j.val:ℝ)*(2/(d+1:ℝ))^(n-j.val) := by
  simpa only [Matrix.l2_opNorm_toEuclideanCLM,Fintype.card_fin] using
    radialChoiCombination_partialTranspose_norm_le (S:=Fin n) d hd r lam

/-- The same original squared-weight Choi companion, retaining its factor two. -/
theorem radial_second_choi_general (d n r : ℕ) (hd : 0<d) (lam : ℕ → ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      (partialTransposeFirst (radialChoiSecondCombination (S:=Fin n) d r lam))‖ ≤
        2*∑ j : Fin (r+1),(lam j.val)^2*(n.choose j.val:ℝ)*(2/(d+1:ℝ))^(n-j.val) := by
  simpa only [Matrix.l2_opNorm_toEuclideanCLM,Fintype.card_fin] using
    radialChoiSecondCombination_partialTranspose_norm_le (S:=Fin n) d hd r lam

/-- A genuinely signed three-qubit tensor Choi sum. -/
theorem radial_choi_signed_three_qubits :
    ‖partialTransposeFirst (radialChoiCombination (S:=Fin 3) 2 1
      (fun j => if j=0 then 1 else -2))‖ ≤ (80:ℝ)/27 := by
  have h := radialChoiCombination_partialTranspose_norm_le (S:=Fin 3) 2 (by omega) 1
    (fun j => if j=0 then 1 else -2)
  norm_num [Fin.sum_univ_succ,Nat.choose] at h ⊢
  exact h

/-- The corresponding squared-weight sum is a different actual matrix with the expected bound. -/
theorem radial_second_choi_signed_three_qubits :
    ‖partialTransposeFirst (radialChoiSecondCombination (S:=Fin 3) 2 1
      (fun j => if j=0 then 1 else -2))‖ ≤ (304:ℝ)/27 := by
  have h := radialChoiSecondCombination_partialTranspose_norm_le (S:=Fin 3) 2 (by omega) 1
    (fun j => if j=0 then 1 else -2)
  norm_num [Fin.sum_univ_succ,Nat.choose] at h ⊢
  exact h

/-- No nonzero subset is manufactured when the coefficient order exceeds the site count. -/
theorem radial_choi_order_above_sites :
    radialChoiCombination (S:=Fin 1) 2 2 (fun j => if j=2 then 7 else 0)=0 := by
  have h := radialChoiCombination_partialTranspose_norm_le (S:=Fin 1) 2 (by omega) 2
    (fun j => if j=2 then 7 else 0)
  norm_num [Fin.sum_univ_succ,Nat.choose] at h
  have hzero : partialTransposeFirst
      (radialChoiCombination (S:=Fin 1) 2 2 (fun j => if j=2 then 7 else 0))=0 := by
    simpa only [norm_le_zero_iff] using h
  ext p q
  exact congrArg (fun M => M (q.1,p.2) (p.1,q.2)) hzero

/-- d=1 is intentionally a bound case: the actual R0 is zero, not norm one. -/
theorem radial_choi_R0_dimension_one : radialChoiR0 1=0 := by
  ext ⟨i,r⟩ ⟨j,s⟩
  fin_cases i
  fin_cases r
  fin_cases j
  fin_cases s
  norm_num [radialChoiR0,radialChoiPhi,unitaryBellProjector,unitaryBellVector,
    Matrix.vecMulVec_apply,Matrix.one_apply]

/-- The empty tensor is a scalar identity even when its local index type is empty. -/
theorem tensor_zero_sites (I : Type*) [Fintype I] [DecidableEq I]
    (A : Fin 0 → Matrix I I ℂ) : ‖wickTensorMatrix A‖=1 := by
  rw [wickTensorMatrix_norm]
  simp

/-- A nonempty tensor with empty local output has the actual zero operator norm. -/
theorem tensor_empty_local (n : ℕ) (A : Fin (n+1) → Matrix (Fin 0) (Fin 0) ℂ) :
    ‖wickTensorMatrix A‖=0 := by
  have h : wickTensorMatrix A=0 := Subsingleton.elim _ _
  rw [h,norm_zero]

/-- Zero coefficients give the genuine zero Choi matrix, before applying any norm estimate. -/
theorem radial_choi_zero_weights (d n r : ℕ) :
    radialChoiCombination (S:=Fin n) d r (fun _ => 0)=0 := by
  simp [radialChoiCombination]

end CertificationGaussian.Consumers
