import LocalCertification.Quantum.StateMixture
import LocalCertification.Quantum.ProductMeasurement

set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix
noncomputable section
namespace LocalCertification.Quantum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The literal target-state mixture used for exact fidelity calibration. -/
def targetMixture (ψ : QIT.PureVector I) (ρ : QIT.State I) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : QIT.State I where
  matrix := t • ψ.state.matrix + (1-t) • ρ.matrix
  pos := (ψ.state.pos.smul ht0).add (ρ.pos.smul (sub_nonneg.mpr ht1))
  trace_eq_one := by
    simp only [Matrix.trace_add, Matrix.trace_smul, ψ.state.trace_eq_one, ρ.trace_eq_one]
    rw [← add_smul]
    simp

theorem targetMixture_fidelity (ψ : QIT.PureVector I) (ρ : QIT.State I) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pureTargetFidelity ψ (targetMixture ψ ρ t ht0 ht1) =
      t + (1-t)*pureTargetFidelity ψ ρ := by
  simp only [pureTargetFidelity, targetMixture, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul,
    ψ.state_matrix_mul_self, ψ.state.trace_eq_one, Complex.one_re, mul_one]

theorem targetMixture_basisBorn (ψ : QIT.PureVector I) (ρ : QIT.State I) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (U : ↥(unitary (Matrix I I ℂ))) (x : I) :
    basisBorn U (targetMixture ψ ρ t ht0 ht1) x =
      t*basisBorn U ψ.state x + (1-t)*basisBorn U ρ x := by
  simp only [basisBorn_trace, targetMixture, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]

/-- Any existing uniform PSD floor is retained with the exact mixture coefficient. -/
theorem targetMixture_floor (ψ : QIT.PureVector I) (ρ ω : QIT.State I) (κ t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hρ : (ρ.matrix - κ • ω.matrix).PosSemidef) :
    ((targetMixture ψ ρ t ht0 ht1).matrix - ((1-t)*κ) • ω.matrix).PosSemidef := by
  change (t • ψ.state.matrix + (1-t) • ρ.matrix - ((1-t)*κ) • ω.matrix).PosSemidef
  rw [add_sub_assoc, ← smul_smul, ← smul_sub]
  exact (ψ.state.pos.smul ht0).add (hρ.smul (sub_nonneg.mpr ht1))

/-- Calibration parameter for a low-state overlap l below the requested baseline b. -/
def calibrationAlpha (b l : ℝ) : ℝ := (b-l)/(1-l)

theorem calibrationAlpha_bounds {b l : ℝ} (_hb0 : 0 < b) (hb1 : b < 1)
    (hl0 : 0 ≤ l) (hlb : l < b) : 0 ≤ calibrationAlpha b l ∧ calibrationAlpha b l ≤ b := by
  have hl1 : 0 < 1-l := sub_pos.mpr (hlb.trans hb1)
  constructor
  · exact (div_pos (sub_pos.mpr hlb) hl1).le
  · apply (div_le_iff₀ hl1).mpr
    nlinarith

theorem calibrationAlpha_exact {b l : ℝ} (hl1 : l < 1) :
    calibrationAlpha b l + (1-calibrationAlpha b l)*l = b := by
  unfold calibrationAlpha
  field_simp [ne_of_gt (sub_pos.mpr hl1)]
  ring

theorem calibrationError_formula {b l : ℝ} (hl1 : l < 1) :
    b-calibrationAlpha b l = (1-b)*l/(1-l) := by
  unfold calibrationAlpha
  field_simp [ne_of_gt (sub_pos.mpr hl1)]
  ring

theorem calibrationError_bounds {b l : ℝ} (_hb0 : 0 < b) (hb1 : b < 1)
    (hl0 : 0 ≤ l) (hlb : l < b) :
    0 ≤ b-calibrationAlpha b l ∧ b-calibrationAlpha b l ≤ l := by
  have hl1 : l < 1 := hlb.trans hb1
  rw [calibrationError_formula hl1]
  constructor
  · positivity
  · apply (div_le_iff₀ (sub_pos.mpr hl1)).mpr
    nlinarith [mul_nonneg hl0 (sub_nonneg.mpr hlb.le)]

end LocalCertification.Quantum
