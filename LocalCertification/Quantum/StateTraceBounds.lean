import LocalCertification.Quantum.StateMixture
import CertificationGaussian.PositiveTensorTrace
import QIT.States.Schatten

set_option autoImplicit false
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
namespace LocalCertification.Quantum
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every physical mixed state pairs an arbitrary complex operator with modulus at most its L2 operator norm. -/
theorem state_trace_norm_le (ρ : QIT.State I) (A : Matrix I I ℂ) :
    ‖(ρ.matrix*A).trace‖ ≤ ‖A‖ := by
  have h := CertificationGaussian.posSemidef_trace_mul_norm_le ρ.matrix A ρ.pos
  simpa only [ρ.trace_eq_one, Complex.one_re, mul_one, Matrix.l2_opNorm_toEuclideanCLM] using h

theorem state_trace_re_abs_le (ρ : QIT.State I) (A : Matrix I I ℂ) :
    |(ρ.matrix*A).trace.re| ≤ ‖A‖ :=
  (Complex.abs_re_le_norm _).trans (state_trace_norm_le ρ A)

/-- Positivity of both actual matrix factors implies nonnegative trace pairing. -/
theorem state_trace_nonneg (ρ : QIT.State I) (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    0 ≤ (ρ.matrix*A).trace.re :=
  QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten ρ.pos hA

/-- Trace against a physical mixed state is monotone in the genuine Loewner order. -/
theorem state_trace_mono (ρ : QIT.State I) {A B : Matrix I I ℂ} (hAB : A ≤ B) :
    (ρ.matrix*A).trace.re ≤ (ρ.matrix*B).trace.re := by
  rw [Matrix.trace_mul_comm ρ.matrix A, Matrix.trace_mul_comm ρ.matrix B]
  exact QIT.cMatrix_trace_mul_le_of_le_posSemidef_right ρ.pos hAB

theorem state_trace_scalar (ρ : QIT.State I) (c : ℝ) :
    (ρ.matrix*(c • (1 : Matrix I I ℂ))).trace.re = c := by
  simp only [Matrix.mul_smul, Matrix.trace_smul, ρ.trace_eq_one,
    Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]

/-- Operator error controls all physical input means simultaneously, without a state-dependent constant. -/
theorem state_trace_error (ρ : QIT.State I) (A B : Matrix I I ℂ) {η : ℝ}
    (h : ‖A-B‖ ≤ η) : |(ρ.matrix*A).trace.re-(ρ.matrix*B).trace.re| ≤ η := by
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] using
    (state_trace_re_abs_le ρ (A-B)).trans h

/-- The literal affine target envelope has the intended fidelity trace on every mixed state. -/
theorem state_trace_target_envelope (ψ : QIT.PureVector I) (ρ : QIT.State I) (c : ℝ) :
    (ρ.matrix*(ψ.state.matrix+c • (1-ψ.state.matrix))).trace.re =
      c+(1-c)*pureTargetFidelity ψ ρ := by
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Complex.add_re, Complex.sub_re,
    Complex.smul_re, smul_eq_mul, ρ.trace_eq_one, Complex.one_re]
  rw [Matrix.trace_mul_comm ρ.matrix ψ.state.matrix]
  unfold pureTargetFidelity
  ring

/-- The Loewner envelopes and operator approximation give affine bounds uniform in the mixed input. -/
theorem state_trace_envelopes (ψ : QIT.PureVector I) (ρ : QIT.State I)
    (A B : Matrix I I ℂ) (l u η : ℝ)
    (hl : ψ.state.matrix+l • (1-ψ.state.matrix) ≤ A)
    (hu : A ≤ ψ.state.matrix+u • (1-ψ.state.matrix))
    (he : ‖B-A‖ ≤ η) :
    l+(1-l)*pureTargetFidelity ψ ρ-η ≤ (ρ.matrix*B).trace.re ∧
    (ρ.matrix*B).trace.re ≤ u+(1-u)*pureTargetFidelity ψ ρ+η := by
  have h1 := state_trace_mono ρ hl
  have h2 := state_trace_mono ρ hu
  rw [state_trace_target_envelope] at h1 h2
  have he' := abs_le.mp (state_trace_error ρ B A he)
  constructor <;> linarith

/-- A scalar Loewner upper bound gives the uniform numerical second-moment bound. -/
theorem state_trace_upper_scalar (ρ : QIT.State I) (M : Matrix I I ℂ) (V : ℝ)
    (h : M ≤ V • (1 : Matrix I I ℂ)) : (ρ.matrix*M).trace.re ≤ V := by
  simpa only [state_trace_scalar] using state_trace_mono ρ h

end LocalCertification.Quantum
