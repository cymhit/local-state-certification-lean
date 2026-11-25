import LocalCertification.Information.FiniteDomination
import LocalCertification.Quantum.CalibrationFloor

set_option autoImplicit false
open Matrix MeasureTheory InformationTheory LocalCertification.Information
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

/-- A fixed target/uniform mixture used only for the degree-zero logarithmic lower bound. -/
def constantLowState (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) : QIT.State (CertificationGaussian.QuditIndex d n) :=
  targetMixture ψ (quditMaximallyMixed d n) (b/2) (by linarith) (by linarith)

theorem constantLowState_fidelity (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) :
    pureTargetFidelity ψ (constantLowState ψ b hb0 hb1)=b/2+(1-b/2)*((d:ℝ)^n)⁻¹ := by
  rw [constantLowState,targetMixture_fidelity,quditMaximallyMixed_fidelity]

theorem constantLowState_promised (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) (hD : ((d:ℝ)^n)⁻¹≤b/2) :
    pureTargetFidelity ψ (constantLowState ψ b hb0 hb1)≤b := by
  rw [constantLowState_fidelity]
  have hD0 : (0:ℝ)≤((d:ℝ)^n)⁻¹ := by positivity
  nlinarith

theorem constantLowState_productBorn (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U (constantLowState ψ b hb0 hb1) x=
      (b/2)*productBorn d n U ψ.state x+(1-b/2)*((d:ℝ)^n)⁻¹ := by
  change basisBorn ⟨_,_⟩ (targetMixture ψ (quditMaximallyMixed d n) (b/2) _ _) x=_
  rw [targetMixture_basisBorn,basisBorn_quditMaximallyMixed]
  rfl

/-- Genuine denominator atoms are positive and dominate the target's own actual Born law. -/
theorem constantLowState_domination (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (x : CertificationGaussian.QuditIndex d n) :
    0<productBorn d n U (constantLowState ψ b hb0 hb1) x ∧
      (b/2)*productBorn d n U ψ.state x≤productBorn d n U (constantLowState ψ b hb0 hb1) x := by
  rw [constantLowState_productBorn]
  have hp := productBorn_nonneg d n U ψ.state x
  have hd : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hrem : (0:ℝ)<(1-b/2)*((d:ℝ)^n)⁻¹ := mul_pos (by linarith) (by positivity)
  constructor <;> nlinarith

/-- A true per-copy information bound uniform in all continuously chosen product bases and targets. -/
theorem constantLowState_klDiv (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) (U : Fin n → CertificationGaussian.LocalUnitary d) :
    klDiv (productBornMeasure d n U ψ.state)
      (productBornMeasure d n U (constantLowState ψ b hb0 hb1))≤ENNReal.ofReal (4/b+2) := by
  have h := productBornMeasure_klDiv_le_domination d n U ψ.state (constantLowState ψ b hb0 hb1)
    (b/2) (by linarith) (fun x => (constantLowState_domination ψ b hb0 hb1 U x).1)
    (fun x => (constantLowState_domination ψ b hb0 hb1 U x).2)
  convert h using 1
  congr 1
  ring

end LocalCertification.Quantum
