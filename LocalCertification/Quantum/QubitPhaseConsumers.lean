import LocalCertification.Quantum.QubitWeylPhase
import LocalCertification.Quantum.CompleteBornRecord

set_option autoImplicit false
open Matrix Classical CertificationGaussian MeasureTheory
open scoped BigOperators ComplexOrder
noncomputable section
namespace LocalCertification.Quantum

variable {n : ℕ}

/-- The exact diagonal unitary changing conventional Pauli orbit columns into canonical Weyl columns. -/
def qubitPhaseDiagonal (n : ℕ) : Matrix (WeylLabel 2 n) (WeylLabel 2 n) ℂ :=
  Matrix.diagonal qubitTensorPhase

theorem qubitPhaseDiagonal_unitary :
    qubitPhaseDiagonal n ∈ unitary (Matrix (WeylLabel 2 n) (WeylLabel 2 n) ℂ) := by
  have h (u : WeylLabel 2 n) : star (qubitTensorPhase u)*qubitTensorPhase u=1 := by
    rw [mul_comm,qubitTensorPhase_mul_star]
  constructor
  · change (qubitPhaseDiagonal n)ᴴ*qubitPhaseDiagonal n=1
    rw [qubitPhaseDiagonal,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    simp only [Pi.star_apply,h,Matrix.diagonal_one]
  · change qubitPhaseDiagonal n*(qubitPhaseDiagonal n)ᴴ=1
    rw [qubitPhaseDiagonal,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    simp only [Pi.star_apply,qubitTensorPhase_mul_star,Matrix.diagonal_one]

theorem qubit_pauli_orbit_matrix (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    unitaryOrbitMatrix quditWeyl ψ=unitaryOrbitMatrix pauliTensor ψ*qubitPhaseDiagonal n := by
  ext i u
  simp [unitaryOrbitMatrix,qubit_pauli_orbit_vector,qubitPhaseDiagonal,
    Matrix.mul_diagonal,PiLp.smul_apply,mul_comm]

/-- Gram matrices are unitarily conjugate, rather than incorrectly asserted entrywise equal. -/
theorem qubit_pauli_gram_conjugation (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    unitaryOrbitGram quditWeyl ψ=(qubitPhaseDiagonal n)ᴴ*
      unitaryOrbitGram pauliTensor ψ*qubitPhaseDiagonal n := by
  simp only [unitaryOrbitGram,qubit_pauli_orbit_matrix,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- Literal average of the conventional Pauli conjugates over the same exact support shell. -/
def pauliShellMatrix (ρ : QIT.State (QuditIndex 2 n)) (j : ℕ) :
    Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ :=
  ((weylShell 2 n j).card : ℝ)⁻¹ •
    ∑ u ∈ weylShell 2 n j,pauliTensor u*ρ.matrix*(pauliTensor u)ᴴ

theorem pauliShellMatrix_eq_weyl (ρ : QIT.State (QuditIndex 2 n)) (j : ℕ) :
    pauliShellMatrix ρ j=weylShellMatrix ρ j := by
  simp only [pauliShellMatrix,weylShellMatrix,quditWeyl_pauli_conjugation]

/-- The conventional Pauli shell is a genuine normalized QIT state. -/
def pauliShellState (ρ : QIT.State (QuditIndex 2 n)) (j : ℕ) (hj : j≤n) :
    QIT.State (QuditIndex 2 n) where
  matrix := pauliShellMatrix ρ j
  pos := by rw [pauliShellMatrix_eq_weyl]; exact weylShellMatrix_pos ρ j
  trace_eq_one := by rw [pauliShellMatrix_eq_weyl]; exact weylShellMatrix_trace (by norm_num) ρ hj

theorem pauliShellState_eq_weyl (ρ : QIT.State (QuditIndex 2 n)) (j : ℕ) (hj : j≤n) :
    pauliShellState ρ j hj=weylShellState (by norm_num) ρ j hj := by
  apply QIT.State.ext
  exact pauliShellMatrix_eq_weyl ρ j

/-- All continuous product-basis readout laws are exactly the same for the two shell presentations. -/
theorem qubit_pauli_shell_born_law (ρ : QIT.State (QuditIndex 2 n)) (j : ℕ) (hj : j≤n)
    (U : Fin n → LocalUnitary 2) :
    productBornMeasure 2 n U (pauliShellState ρ j hj)=
      productBornMeasure 2 n U (weylShellState (by norm_num) ρ j hj) := by
  rw [pauliShellState_eq_weyl]

/-- The equality retains the complete arbitrary measurable setting label and outcome record. -/
theorem qubit_pauli_shell_complete_law {H : Type*} [MeasurableSpace H]
    (ρ : QIT.State (QuditIndex 2 n)) (j : ℕ) (hj : j≤n)
    (setting : H → Fin n → LocalUnitary 2) (hm : Measurable setting) (μ : Measure H) :
    completeBornRecordLaw (pauliShellState ρ j hj) setting hm μ=
      completeBornRecordLaw (weylShellState (by norm_num) ρ j hj) setting hm μ := by
  rw [pauliShellState_eq_weyl]

/-- The actual Gaussian conjugation model is phase independent for every real signed weight. -/
theorem qubit_pauli_gaussian_conjugation (a : WeylLabel 2 n → ℝ)
    (g : Fin 2 × QuditIndex 2 n → ℝ) :
    unitaryGaussianConjugation quditWeyl a g=unitaryGaussianConjugation pauliTensor a g := by
  simp only [unitaryGaussianConjugation,unitaryWeightedRankOne,quditWeyl_pauli_conjugation]

end LocalCertification.Quantum
