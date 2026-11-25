import LocalCertification.Quantum.IsometryEnvelopes

set_option autoImplicit false
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
namespace LocalCertification.Quantum
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private theorem trace_affine_matrix (ρ : QIT.State I) (P : Matrix I I ℂ) (c : ℝ) :
    (ρ.matrix*(P+c • (1-P))).trace.re = c+(1-c)*(ρ.matrix*P).trace.re := by
  simp only [Matrix.mul_add,Matrix.mul_smul,Matrix.mul_sub,Matrix.mul_one,
    Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,Complex.add_re,Complex.sub_re,
    Complex.smul_re,smul_eq_mul,ρ.trace_eq_one,Complex.one_re]
  ring

/-- Exact low-spectrum intervals, actual CFC-column target error, and actual operator error control
every mixed-state mean. No pure-state or target-independent-input restriction is imposed. -/
theorem spectral_score_mean_bounds (ψ : QIT.PureVector I) (ρ : QIT.State I)
    (Q : Matrix I J ℂ) (hQ : Qᴴ*Q=1) (i : J) (c : J → ℝ) (hc : c i=1)
    (l u ε τ : ℝ) (hl0 : l≤0) (hu0 : 0≤u)
    (hcl : ∀ j, j≠i → l≤c j) (hcu : ∀ j, j≠i → c j≤u)
    (B : Matrix I I ℂ)
    (hB : ‖B-Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ‖≤ε)
    (hP : ‖Q*Matrix.single i i (1:ℂ)*Qᴴ-ψ.state.matrix‖≤τ) :
    l+(1-l)*pureTargetFidelity ψ ρ-(ε+|1-l| *τ) ≤ (ρ.matrix*B).trace.re ∧
    (ρ.matrix*B).trace.re ≤ u+(1-u)*pureTargetFidelity ψ ρ+(ε+|1-u| *τ) := by
  let P := Q*Matrix.single i i (1:ℂ)*Qᴴ
  let A := Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ
  have he := isometry_diagonal_envelopes Q hQ i c hc l u hl0 hu0 hcl hcu
  have hlo := state_trace_mono ρ he.1
  have hup := state_trace_mono ρ he.2
  change (ρ.matrix*(P+l • (1-P))).trace.re ≤ (ρ.matrix*A).trace.re at hlo
  change (ρ.matrix*A).trace.re ≤ (ρ.matrix*(P+u • (1-P))).trace.re at hup
  rw [trace_affine_matrix] at hlo hup
  have hb := abs_le.mp (state_trace_error ρ B A hB)
  have hp : |(ρ.matrix*P).trace.re-pureTargetFidelity ψ ρ|≤τ := by
    have h := state_trace_error ρ P ψ.state.matrix hP
    rw [Matrix.trace_mul_comm ρ.matrix ψ.state.matrix] at h
    exact h
  have hm (v : ℝ) : |(1-v)*((ρ.matrix*P).trace.re-pureTargetFidelity ψ ρ)|≤|1-v| *τ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  have hml := abs_le.mp (hm l)
  have hmu := abs_le.mp (hm u)
  constructor <;> nlinarith

/-- A uniform upper bound on all real coefficients also bounds the zero spectrum off the range. -/
theorem isometry_diagonal_upper (Q : Matrix I J ℂ) (hQ : Qᴴ*Q=1)
    (c : J → ℝ) (e : ℝ) (he : 0≤e) (hc : ∀ j,c j≤e) :
    Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ ≤ e • (1 : Matrix I I ℂ) := by
  have hd : (e • (1 : Matrix J J ℂ)-Matrix.diagonal (fun j => (c j:ℂ))).PosSemidef := by
    have hid : e • (1 : Matrix J J ℂ) = Matrix.diagonal (fun _ => (e:ℂ)) := by
      ext a b
      by_cases hab : a=b <;> simp [hab]
    rw [hid,Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro j
    simpa [Complex.nonneg_iff] using hc j
  have h := (hd.mul_mul_conjTranspose_same Q).add ((isometry_range_complement_pos Q hQ).smul he)
  apply Matrix.le_iff.mpr
  convert h using 1
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,smul_sub]
  abel

/-- The scalar variance scale plus an actual low-spectrum operator and a norm remainder gives a
uniform numerical second-moment trace bound for every physical input. -/
theorem spectral_score_second_bound (ρ : QIT.State I)
    (Q : Matrix I J ℂ) (hQ : Qᴴ*Q=1) (c : J → ℝ) (e ν ε : ℝ)
    (he : 0≤e) (hc : ∀ j,c j≤e) (M : Matrix I I ℂ)
    (hM : ‖M-(ν • (1 : Matrix I I ℂ)+Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ)‖≤ε) :
    (ρ.matrix*M).trace.re ≤ ν+e+ε := by
  have hlow := state_trace_mono ρ (isometry_diagonal_upper Q hQ c e he hc)
  rw [state_trace_scalar] at hlow
  have herr := (abs_le.mp (state_trace_error ρ M
    (ν • (1 : Matrix I I ℂ)+Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ) hM)).2
  simp only [Matrix.mul_add,Matrix.trace_add,Complex.add_re,state_trace_scalar] at herr
  linarith

end LocalCertification.Quantum
