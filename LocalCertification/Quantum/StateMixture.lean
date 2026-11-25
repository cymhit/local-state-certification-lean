import LocalCertification.Quantum.Boundary
import QIT.States.MaximallyMixed

set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix
noncomputable section
namespace LocalCertification.Quantum

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- Literal real-weighted sum of actual QIT density matrices. -/
def weightedStateMatrix (ρ : J → QIT.State I) (w : J → ℝ) : Matrix I I ℂ :=
  ∑ i, w i • (ρ i).matrix

theorem weightedStateMatrix_pos (ρ : J → QIT.State I) (w : J → ℝ)
    (hw : ∀ i, 0 ≤ w i) : (weightedStateMatrix ρ w).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => (ρ i).pos.smul (hw i))

theorem weightedStateMatrix_trace (ρ : J → QIT.State I) (w : J → ℝ) :
    (weightedStateMatrix ρ w).trace = ((∑ i, w i : ℝ) : ℂ) := by
  simp [weightedStateMatrix, Matrix.trace_sum, Matrix.trace_smul, QIT.State.trace_eq_one, Complex.real_smul]

theorem pureTargetFidelity_nonneg (ψ : QIT.PureVector I) (ρ : QIT.State I) :
    0 ≤ pureTargetFidelity ψ ρ := by
  rw [pureTargetFidelity_eq_squaredFidelity]
  exact ρ.squaredFidelity_nonneg ψ.state

theorem pureTargetFidelity_self (ψ : QIT.PureVector I) : pureTargetFidelity ψ ψ.state = 1 := by
  unfold pureTargetFidelity
  rw [ψ.state_matrix_mul_self, ψ.state.trace_eq_one]
  rfl

/-- Pure-target fidelity is affine for the actual weighted matrix sum. -/
theorem weightedStateMatrix_pairing (ψ : QIT.PureVector I) (ρ : J → QIT.State I) (w : J → ℝ) :
    (ψ.state.matrix * weightedStateMatrix ρ w).trace.re =
      ∑ i, w i * pureTargetFidelity ψ (ρ i) := by
  simp [weightedStateMatrix, Finset.mul_sum, Matrix.trace_sum,
    Matrix.trace_smul, Complex.real_smul, pureTargetFidelity]

/-- The unique QIT maximally mixed construction on the sole qudit index. -/
def quditMaximallyMixed (d n : ℕ) [NeZero d] : QIT.State (CertificationGaussian.QuditIndex d n) := by
  let : Nonempty (CertificationGaussian.QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  exact QIT.State.maximallyMixed _

theorem quditMaximallyMixed_matrix (d n : ℕ) [NeZero d] :
    (quditMaximallyMixed d n).matrix = ((d : ℝ)^n)⁻¹ •
      (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) := by
  simp only [quditMaximallyMixed, QIT.State.maximallyMixed_matrix, qudit_card, Nat.cast_pow]
  ext x y
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]

theorem quditMaximallyMixed_fidelity (d n : ℕ) [NeZero d]
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) :
    pureTargetFidelity ψ (quditMaximallyMixed d n) = ((d : ℝ)^n)⁻¹ := by
  rw [pureTargetFidelity, quditMaximallyMixed_matrix, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, ψ.state.trace_eq_one]
  simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]

end LocalCertification.Quantum
