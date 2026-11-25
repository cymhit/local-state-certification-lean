import LocalCertification.Quantum.RadialWeylOrbit
import CertificationGaussian.ReadoutLinearFullControl

set_option autoImplicit false
open Matrix CertificationGaussian Classical
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

/-- Weyl labels below the linear weight cutoff. -/
abbrev LinearWeylIndex (d n : ℕ) [NeZero d] (ε : ℝ) :=
  ↥(radialLinearLowLabels ε n (0 : ZMod d × ZMod d))

/-- Explicitly identify the actual linear-cutoff set with canonical Weyl weights at floor(epsilon*n). -/
def linearWeylIndexEquiv (d n : ℕ) [NeZero d] (ε : ℝ) :
    LinearWeylIndex d n ε ≃ LowWeylIndex d n (radialLinearWeightCutoff ε n) where
  toFun w := ⟨w.val,(Finset.mem_filter.mp w.property).2⟩
  invFun w := ⟨w.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,w.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def linearWeylIdentity (d n : ℕ) [NeZero d] (ε : ℝ) : LinearWeylIndex d n ε :=
  (linearWeylIndexEquiv d n ε).symm (lowWeylIdentity d n (radialLinearWeightCutoff ε n))

@[simp] theorem linearWeylIdentity_val (ε : ℝ) : (linearWeylIdentity d n ε).val=0 := rfl

@[simp] theorem linearWeylLow_identity (ε : ℝ) :
    radialLinearLowOrbitFamily d n ε localWeylFin 0 (linearWeylIdentity d n ε)=1 := quditWeyl_zero

/-- The original coefficient at the real identity is one, and every other column has positive weight. -/
theorem linearWeyl_coefficients (r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (h0 : lam 0=1) (hd : 0<d) :
    radialFirstCoefficient d r lam (weylWeight (linearWeylIdentity d n ε).val)=1 ∧
      ∀ w : LinearWeylIndex d n ε,w≠linearWeylIdentity d n ε →
        LocalCertification.Extremal.lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)≤radialFirstCoefficient d r lam (weylWeight w.val) ∧
        radialFirstCoefficient d r lam (weylWeight w.val)≤LocalCertification.Extremal.upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam) := by
  constructor
  · simpa [radialFirstCoefficient_zero,weylWeight,weylSupport] using h0
  · intro w hw
    apply radialFirstCoefficient_envelope d r hd lam
    apply Nat.pos_of_ne_zero
    intro hz
    apply hw
    apply Subtype.ext
    exact (weylWeight_eq_zero w.val).mp hz

def linearWeylPolarMatrix (ε : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    Matrix (QuditIndex d n) (LinearWeylIndex d n ε) ℂ :=
  matrixPolarCorrection (unitaryOrbitMatrix (radialLinearLowOrbitFamily d n ε localWeylFin 0) ψ)

/-- The physical target is the identity column of the same actual linear-cutoff CFC correction. -/
theorem linearWeyl_target_projector {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (ε : ℝ) (μ : MeasureTheory.Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (lam : ℕ → ℝ) (C₁ C₂ : ℝ)
    (ψ : QIT.PureVector (QuditIndex d n))
    (h : radialLinearReadoutPolarControl d n r ε μ record lam localWeylFin 0 C₁ C₂ (WithLp.toLp 2 ψ.amp)) :
    let Q := linearWeylPolarMatrix ε (WithLp.toLp 2 ψ.amp)
    ‖Q*Matrix.single (linearWeylIdentity d n ε) (linearWeylIdentity d n ε) (1:ℂ)*Qᴴ-ψ.state.matrix‖≤
      2*((n:ℝ)^3)⁻¹ := by
  dsimp only
  apply isometry_identity_column_error
    (unitaryOrbitMatrix (radialLinearLowOrbitFamily d n ε localWeylFin 0) (WithLp.toLp 2 ψ.amp))
    _ _ (WithLp.toLp 2 ψ.amp) (pure_amp_norm ψ)
  · ext i
    simp [rectangularEuclideanCLM,Matrix.toEuclideanLin,Matrix.toLpLin_apply,unitaryOrbitMatrix]
  · exact h.2.2.1
  · exact h.2.1

/-- Actual B is approximated by the actual linear CFC matrix with the original first coefficients. -/
theorem linearWeyl_first_matrix_error {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (ε : ℝ) (μ : MeasureTheory.Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (C₁ C₂ : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (h : radialLinearReadoutPolarControl d n r ε μ record lam localWeylFin 0 C₁ C₂ ψ) :
    ‖cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.ofLp-
      linearWeylPolarMatrix ε ψ*Matrix.diagonal
        (fun w : LinearWeylIndex d n ε => (radialFirstCoefficient d r lam (weylWeight w.val):ℂ))*
      (linearWeylPolarMatrix ε ψ)ᴴ‖≤C₁*((n:ℝ)^3)⁻¹ := by
  have he := h.2.2.2.1
  change ‖rectangularEuclideanCLM _-rectangularEuclideanCLM _‖≤_ at he
  rw [← rectangularEuclideanCLM_sub,rectangularEuclideanCLM_norm] at he
  exact he

/-- Actual full M, including its original scalar, uses the very same linear CFC matrix. -/
theorem linearWeyl_full_matrix_error {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (ε : ℝ) (μ : MeasureTheory.Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (C₁ C₂ CM : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (h : radialLinearReadoutFullControl d n r ε μ record lam localWeylFin 0 C₁ C₂ CM ψ) :
    ‖cardinalityReadoutSecond d μ record r lam ((d:ℝ)^n) ψ.ofLp-
      (cardinalityReadoutTraceScale d n r (fun j => (lam j)^2) •
        (1:Matrix (QuditIndex d n) (QuditIndex d n) ℂ)+
      linearWeylPolarMatrix ε ψ*Matrix.diagonal
        (fun w : LinearWeylIndex d n ε => (radialSecondCoefficient d r lam (weylWeight w.val):ℂ))*
      (linearWeylPolarMatrix ε ψ)ᴴ)‖≤(C₂+CM)*((n:ℝ)^3)⁻¹ := by
  have he := h.2.2
  change ‖rectangularEuclideanCLM _-rectangularEuclideanCLM _‖≤_ at he
  rw [← rectangularEuclideanCLM_sub,rectangularEuclideanCLM_norm,sub_sub] at he
  exact he

end LocalCertification.Quantum
