import LocalCertification.Quantum.WeylShellState
import LocalCertification.Quantum.BornMeasure
import LocalCertification.Quantum.WeylGaussianChaos
import LocalCertification.Quantum.WeylOrbit

set_option autoImplicit false
open Matrix Classical CertificationGaussian
open scoped BigOperators ComplexConjugate
noncomputable section
namespace LocalCertification.Quantum

/-- Conventional qubit Pauli matrices; labels retain the canonical shift/phase ordering. -/
def pauliRepresentative (u : ZMod 2 × ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if u.1=0 then (if u.2=0 then 1 else !![1,0;0,-1])
  else (if u.2=0 then !![0,1;1,0] else !![0,-Complex.I;Complex.I,0])

/-- Only the XZ label carries the nontrivial phase. -/
def qubitWeylPhase (u : ZMod 2 × ZMod 2) : ℂ :=
  if u.1=1 ∧ u.2=1 then -Complex.I else 1

private theorem stdAddChar_two_one : ZMod.stdAddChar (1 : ZMod 2)=(-1:ℂ) := by
  have h := ZMod.stdAddChar_coe (N:=2) (1:ℤ)
  norm_num only [Int.cast_one,Nat.cast_ofNat,mul_one] at h
  rw [show (2:ℂ)*Real.pi*Complex.I/2=(Real.pi:ℂ)*Complex.I by ring] at h
  simpa only [Complex.exp_pi_mul_I] using h

/-- The actual canonical Fin2 Weyl representatives are I,X,Z and -iY. -/
theorem localWeylFin_two_phase (u : ZMod 2 × ZMod 2) :
    localWeylFin u=qubitWeylPhase u • pauliRepresentative u := by
  obtain ⟨a,b⟩ := u
  have hc (z : ZMod 2) : z=0 ∨ z=1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hadd : (1:ZMod 2)+1=0 := by decide
  have he0 : weylIndexEquiv 2 0=0 := rfl
  have he1 : weylIndexEquiv 2 1=1 := rfl
  rcases hc a with rfl|rfl <;> rcases hc b with rfl|rfl
  all_goals ext x y; fin_cases x <;> fin_cases y
  all_goals norm_num [localWeylFin_apply,he0,he1,hadd,
    pauliRepresentative,qubitWeylPhase,stdAddChar_two_one]

theorem canonical_qubit_XZ_eq_neg_I_Y :
    localWeylFin ((1,1) : ZMod 2 × ZMod 2)=(-Complex.I) • !![0,-Complex.I;Complex.I,0] := by
  simpa [qubitWeylPhase,pauliRepresentative] using localWeylFin_two_phase (1,1)

theorem qubitWeylPhase_mul_star (u : ZMod 2 × ZMod 2) :
    qubitWeylPhase u*star (qubitWeylPhase u)=1 := by
  simp only [qubitWeylPhase]
  split_ifs <;> norm_num

/-- The literal product of canonical X and Z is -i times the conventional Y. -/
theorem canonical_qubit_X_mul_Z :
    localWeylFin ((1,0) : ZMod 2 × ZMod 2)*localWeylFin ((0,1) : ZMod 2 × ZMod 2)=
      (-Complex.I) • !![0,-Complex.I;Complex.I,0] := by
  rw [localWeylFin_two_phase,localWeylFin_two_phase]
  ext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [qubitWeylPhase,pauliRepresentative,Matrix.mul_apply,Fin.sum_univ_two]

/-- Conventional Pauli tensor representatives on the same physical index and same support labels. -/
def pauliTensor {n : ℕ} (u : WeylLabel 2 n) : Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ :=
  tensorMatrix (fun i => pauliRepresentative (u i))

def qubitTensorPhase {n : ℕ} (u : WeylLabel 2 n) : ℂ := ∏ i,qubitWeylPhase (u i)

theorem qubitTensorPhase_mul_star {n : ℕ} (u : WeylLabel 2 n) :
    qubitTensorPhase u*star (qubitTensorPhase u)=1 := by
  simp only [qubitTensorPhase,star_prod,← Finset.prod_mul_distrib,qubitWeylPhase_mul_star,
    Finset.prod_const_one]

/-- The global tensor phase is retained explicitly, including the empty tensor product. -/
theorem quditWeyl_two_phase {n : ℕ} (u : WeylLabel 2 n) :
    quditWeyl u=qubitTensorPhase u • pauliTensor u := by
  ext x y
  simp only [quditWeyl_apply,localWeylFin_two_phase,Matrix.smul_apply,smul_eq_mul,
    Finset.prod_mul_distrib,qubitTensorPhase,pauliTensor,tensorMatrix]

/-- Unit phases cancel in the actual conjugation channel for every complex input matrix. -/
theorem matrix_phase_conjugation {I : Type*} [Fintype I] (c : ℂ) (hc : c*star c=1)
    (V A : Matrix I I ℂ) : (c • V)*A*(c • V)ᴴ=V*A*Vᴴ := by
  rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc,one_smul]

theorem quditWeyl_pauli_conjugation {n : ℕ} (u : WeylLabel 2 n)
    (A : Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ) :
    quditWeyl u*A*(quditWeyl u)ᴴ=pauliTensor u*A*(pauliTensor u)ᴴ := by
  rw [quditWeyl_two_phase]
  exact matrix_phase_conjugation _ (qubitTensorPhase_mul_star u) _ _

/-- Unit phases also cancel in the literal orbit rank-one projector. -/
theorem vecMulVec_phase {I : Type*} (c : ℂ) (hc : c*star c=1) (v : I → ℂ) :
    Matrix.vecMulVec (fun i => c*v i) (fun j => star (c*v j))=
      Matrix.vecMulVec v (fun j => star (v j)) := by
  ext i j
  simp only [Matrix.vecMulVec_apply,star_mul]
  calc
    (c*v i)*(star (v j)*star c)=(c*star c)*(v i*star (v j)) := by ring
    _=v i*star (v j) := by rw [hc,one_mul]

theorem qubit_pauli_orbit_vector {n : ℕ} (u : WeylLabel 2 n)
    (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) (quditWeyl u) ψ=
      qubitTensorPhase u • Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) (pauliTensor u) ψ := by
  rw [quditWeyl_two_phase,map_smul]
  rfl

theorem qubit_pauli_orbit_projector {n : ℕ} (u : WeylLabel 2 n)
    (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    Matrix.vecMulVec (fun i => Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) (quditWeyl u) ψ i)
      (fun j => star (Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) (quditWeyl u) ψ j))=
    Matrix.vecMulVec (fun i => Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) (pauliTensor u) ψ i)
      (fun j => star (Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ) (pauliTensor u) ψ j)) := by
  simp only [qubit_pauli_orbit_vector,PiLp.smul_apply,smul_eq_mul]
  exact vecMulVec_phase _ (qubitTensorPhase_mul_star u) _

theorem qubit_pauli_bell_vector {n : ℕ} (u : WeylLabel 2 n) :
    unitaryBellVector (quditWeyl u)=qubitTensorPhase u • unitaryBellVector (pauliTensor u) := by
  ext i
  simp only [quditWeyl_two_phase,unitaryBellVector,Matrix.smul_apply,
    PiLp.smul_apply,smul_eq_mul]
  ring

theorem qubit_pauli_bell_projector {n : ℕ} (u : WeylLabel 2 n) :
    Matrix.vecMulVec (fun i => unitaryBellVector (quditWeyl u) i)
      (fun j => star (unitaryBellVector (quditWeyl u) j))=
    Matrix.vecMulVec (fun i => unitaryBellVector (pauliTensor u) i)
      (fun j => star (unitaryBellVector (pauliTensor u) j)) := by
  simp only [qubit_pauli_bell_vector,PiLp.smul_apply,smul_eq_mul]
  exact vecMulVec_phase _ (qubitTensorPhase_mul_star u) _

/-- Signed Bell mixtures, and hence their partial transpose, are exactly phase independent. -/
theorem qubit_pauli_weightedBell {n : ℕ} (a : WeylLabel 2 n → ℝ) :
    weightedBellMatrix quditWeyl a=weightedBellMatrix pauliTensor a := by
  simp only [weightedBellMatrix,qubit_pauli_bell_projector]

/-- Conventional Pauli representatives are Hermitian; the canonical XZ Weyl representative is not. -/
theorem pauliRepresentative_adjoint (u : ZMod 2 × ZMod 2) :
    (pauliRepresentative u)ᴴ=pauliRepresentative u := by
  unfold pauliRepresentative
  split_ifs <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    norm_num [Matrix.conjTranspose_apply]

theorem pauliTensor_adjoint {n : ℕ} (u : WeylLabel 2 n) :
    (pauliTensor u)ᴴ=pauliTensor u := by
  rw [pauliTensor,← tensorMatrix_adjoint]
  simp only [pauliRepresentative_adjoint]

theorem pauliTensor_unitary {n : ℕ} (u : WeylLabel 2 n) :
    pauliTensor u ∈ unitary (Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ) := by
  have h := quditWeyl_pauli_conjugation u 1
  rw [Matrix.mul_one,Matrix.mul_one,quditWeyl_mul_adjoint,pauliTensor_adjoint] at h
  constructor <;> simpa only [Matrix.star_eq_conjTranspose,pauliTensor_adjoint] using h.symm

/-- The adjoint orientation used by shell readout is phase independent as well. -/
theorem quditWeyl_pauli_adjoint_conjugation {n : ℕ} (u : WeylLabel 2 n)
    (A : Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ) :
    (quditWeyl u)ᴴ*A*quditWeyl u=(pauliTensor u)ᴴ*A*pauliTensor u := by
  have hc : star (qubitTensorPhase u)*qubitTensorPhase u=1 := by
    rw [mul_comm,qubitTensorPhase_mul_star]
  rw [quditWeyl_two_phase,Matrix.conjTranspose_smul,Matrix.smul_mul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc,one_smul]

end LocalCertification.Quantum
