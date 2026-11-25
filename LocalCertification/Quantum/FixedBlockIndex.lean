import LocalCertification.Quantum.ProductMeasurement
import CertificationGaussian.SphereTransport

set_option autoImplicit false
open Matrix CertificationGaussian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Quantum

/-- A prescribed partition of all physical sites, including their fixed order within each block.
This equivalence is fixed once and is never chosen anew between copies. -/
abbrev FixedBlockPartition (k m : ℕ) := Fin (k*m) ≃ Fin m × Fin k

/-- A fixed labeling of the complete computational bit strings inside one block. -/
def blockLabelEquiv (k : ℕ) : (Fin k → Fin 2) ≃ Fin (2^k) :=
  Fintype.equivFinOfCardEq (by simp)

/-- The actual tensor-product identification of km physical qubits with m qudits of dimension2^k. -/
def fixedBlockIndexEquiv {k m : ℕ} (P : FixedBlockPartition k m) :
    QuditIndex 2 (k*m) ≃ QuditIndex (2^k) m where
  toFun x b := blockLabelEquiv k (fun i => x (P.symm (b,i)))
  invFun y s := (blockLabelEquiv k).symm (y (P s).1) (P s).2
  left_inv x := by
    funext s
    simp
  right_inv y := by
    funext b
    simp

theorem fixedBlockIndexEquiv_component {k m : ℕ} (P : FixedBlockPartition k m)
    (x : QuditIndex 2 (k*m)) (b : Fin m) (i : Fin k) :
    (blockLabelEquiv k).symm (fixedBlockIndexEquiv P x b) i=x (P.symm (b,i)) := by
  simp [fixedBlockIndexEquiv]

/-- No qubits are discarded or duplicated by a prescribed partition, also at m=0. -/
theorem fixedBlock_dimension (k m : ℕ) :
    Fintype.card (QuditIndex 2 (k*m))=Fintype.card (QuditIndex (2^k) m) := by
  simp [QuditIndex,pow_mul]

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Every density state, including every mixed state, is transported bijectively. -/
def stateReindexEquiv (e : I ≃ J) : QIT.State I ≃ QIT.State J where
  toFun ρ := ρ.reindex e
  invFun ρ := ρ.reindex e.symm
  left_inv ρ := by apply QIT.State.ext; ext i j; simp
  right_inv ρ := by apply QIT.State.ext; ext i j; simp

omit [DecidableEq I] [DecidableEq J] in
/-- Simultaneous coordinate reindexing preserves the actual trace pairing. -/
theorem trace_mul_reindex (e : I ≃ J) (A B : Matrix I I ℂ) :
    ((A.submatrix e.symm e.symm)*(B.submatrix e.symm e.symm)).trace=(A*B).trace := by
  rw [Matrix.submatrix_mul_equiv]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/-- The physical pure-target fidelity is exactly unchanged for every input state. -/
theorem pureTargetFidelity_reindex (e : I ≃ J) (ψ : QIT.PureVector I) (ρ : QIT.State I) :
    pureTargetFidelity (ψ.reindex e) (ρ.reindex e)=pureTargetFidelity ψ ρ := by
  unfold pureTargetFidelity
  rw [QIT.PureVector.reindex_state]
  exact congrArg Complex.re (trace_mul_reindex e ψ.state.matrix ρ.matrix)

/-- All orthonormal bases, not only product bases of the individual physical qubits, reindex bijectively. -/
def unitaryReindex (e : I ≃ J) (U : ↥(unitary (Matrix I I ℂ))) : ↥(unitary (Matrix J J ℂ)) :=
  ⟨U.val.submatrix e.symm e.symm,by
    constructor
    · change (U.val.conjTranspose.submatrix e.symm e.symm)*(U.val.submatrix e.symm e.symm)=1
      rw [Matrix.submatrix_mul_equiv]
      simpa only [Matrix.submatrix_one_equiv,Matrix.star_eq_conjTranspose] using congrArg
        (fun A : Matrix I I ℂ => A.submatrix e.symm e.symm) U.property.1
    · change (U.val.submatrix e.symm e.symm)*(U.val.conjTranspose.submatrix e.symm e.symm)=1
      rw [Matrix.submatrix_mul_equiv]
      simpa only [Matrix.submatrix_one_equiv,Matrix.star_eq_conjTranspose] using congrArg
        (fun A : Matrix I I ℂ => A.submatrix e.symm e.symm) U.property.2⟩

theorem unitaryReindex_inverse (e : I ≃ J) (U : ↥(unitary (Matrix I I ℂ))) :
    unitaryReindex e.symm (unitaryReindex e U)=U := by
  apply Subtype.ext
  ext i j
  simp [unitaryReindex]

/-- Reindexing changes neither the complete outcome probability nor the input density matrix. -/
theorem basisBorn_reindex (e : I ≃ J) (U : ↥(unitary (Matrix I I ℂ)))
    (ρ : QIT.State I) (x : I) :
    basisBorn (unitaryReindex e U) (ρ.reindex e) (e x)=basisBorn U ρ x := by
  rw [basisBorn_diagonal,basisBorn_diagonal]
  change (((U.val.conjTranspose.submatrix e.symm e.symm)*(ρ.matrix.submatrix e.symm e.symm)*
    (U.val.submatrix e.symm e.symm)) (e x) (e x)).re=_
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  simp

end LocalCertification.Quantum
