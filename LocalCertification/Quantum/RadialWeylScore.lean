import LocalCertification.Quantum.RadialWeylOrbit
import LocalCertification.Quantum.ReadoutScoreMoments
import LocalCertification.Quantum.HaarWeylOverlap
import LocalCertification.Quantum.SpectralScoreBounds

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter CertificationGaussian LocalCertification.Extremal
open scoped BigOperators Matrix.Norms.L2Operator Topology
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

/-- The original low columns and their actual CFC correction, with the canonical Weyl matrices. -/
def radialWeylPolarMatrix (r : ℕ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    Matrix (QuditIndex d n) (RadialWeylIndex d n r) ℂ :=
  matrixPolarCorrection (unitaryOrbitMatrix (radialLowOrbitFamily d n r localWeylFin 0) ψ)

/-- The B error in the supplied actual radial event is the same L2 matrix operator error. -/
theorem radialWeyl_first_matrix_error {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (C₁ C₂ : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (h : radialReadoutPolarControl d n r μ record lam localWeylFin 0 C₁ C₂ ψ) :
    ‖cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.ofLp-
      radialWeylPolarMatrix r ψ * Matrix.diagonal
        (fun w : RadialWeylIndex d n r => (radialFirstCoefficient d r lam (weylWeight w.val):ℂ)) *
      (radialWeylPolarMatrix r ψ)ᴴ‖≤C₁*((n:ℝ)^3)⁻¹ := by
  have he := h.2.2.2.1
  change ‖rectangularEuclideanCLM _-rectangularEuclideanCLM _‖≤_ at he
  rw [← rectangularEuclideanCLM_sub,rectangularEuclideanCLM_norm] at he
  exact he

/-- Actual low-spectrum approximation implies the original mixed-state fidelity envelopes.
This statement quantifies over every physical input after the target and its good event are fixed. -/
theorem radialWeyl_mean_trace_bounds {Ω : Type*} [MeasurableSpace Ω]
    (hd : 0<d) (r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (h0 : lam 0=1) (C₁ C₂ : ℝ)
    (ψ : QIT.PureVector (QuditIndex d n))
    (h : radialReadoutPolarControl d n r μ record lam localWeylFin 0 C₁ C₂
      (WithLp.toLp 2 ψ.amp)) (ρ : QIT.State (QuditIndex d n)) :
    let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
    let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
    l+(1-l)*pureTargetFidelity ψ ρ-(C₁+2*|1-l|)*((n:ℝ)^3)⁻¹ ≤
      (ρ.matrix*cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.amp).trace.re ∧
    (ρ.matrix*cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.amp).trace.re ≤
      u+(1-u)*pureTargetFidelity ψ ρ+(C₁+2*|1-u|)*((n:ℝ)^3)⁻¹ := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hq : 1<(d:ℝ)+1 := by linarith
  let c : RadialWeylIndex d n r → ℝ := fun w => radialFirstCoefficient d r lam (weylWeight w.val)
  have hc := radialWeyl_coefficients (n:=n) r lam h0 hd
  have he := spectral_score_mean_bounds ψ ρ (radialWeylPolarMatrix r (WithLp.toLp 2 ψ.amp))
    h.1 (radialWeylIdentity d n r) c hc.1
    (lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
    (upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
    (C₁*((n:ℝ)^3)⁻¹) (2*((n:ℝ)^3)⁻¹)
    (envelope_zero_bounds _ hq _).1 (envelope_zero_bounds _ hq _).2
    (fun w hw => (hc.2 w hw).1) (fun w hw => (hc.2 w hw).2) _
    (radialWeyl_first_matrix_error r μ record lam C₁ C₂ _ h)
    (radialWeyl_target_projector r μ record lam C₁ C₂ ψ h)
  have heq (v : ℝ) : C₁*((n:ℝ)^3)⁻¹+|1-v| *(2*((n:ℝ)^3)⁻¹)=
      (C₁+2*|1-v|)*((n:ℝ)^3)⁻¹ := by ring
  simpa only [heq] using he

/-- The very same original high/low bad set, now instantiated at the canonical qudit Weyl family. -/
def radialWeylSphereBad (d n r : ℕ) [NeZero d] (lam : ℕ → ℝ) :
    Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
  radialHighSphereBad d n r lam localWeylFin 0 ∪ radialLowSphereBad d n r localWeylFin 0

/-- Genuine Haar probability and actual Born mean envelopes for all mixed inputs on one event.
The constants and eventual n threshold precede the initial target and all physical inputs. -/
theorem radialWeyl_haar_mean_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (lam : ℕ → ℝ) (h0 : lam 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀∈radialWeylSphereBad d n r lam} ∧
      complexUnitaryHaar (QuditIndex d n)
        {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀∈radialWeylSphereBad d n r lam}≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+2)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex d n) U ψ₀∉radialWeylSphereBad d n r lam →
        ∀ ρ : QIT.State (QuditIndex d n),
        let ψ := haarPureVector ψ₀ U
        let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
        let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
        l+(1-l)*pureTargetFidelity ψ ρ-(C+2*|1-l|)*((n:ℝ)^3)⁻¹ ≤
          ∫ z,cardinalityBornScore (id : LocalUnitary d → LocalUnitary d) r lam
            (WithLp.toLp 2 ψ.amp) z∂haarProductBornLaw d n ρ ∧
        (∫ z,cardinalityBornScore (id : LocalUnitary d → LocalUnitary d) r lam
            (WithLp.toLp 2 ψ.amp) z∂haarProductBornLaw d n ρ)≤
          u+(1-u)*pureTargetFidelity ψ ρ+(C+2*|1-u|)*((n:ℝ)^3)⁻¹ := by
  obtain ⟨C₁,C₂,hC₁,_hC₂,hE⟩ := radialHaarReadoutPolar_haar_eventually d r hd lam
    (0 : ZMod d × ZMod d) localWeylLabel_card
  refine ⟨C₁,hC₁,?_⟩
  filter_upwards [hE] with n hn
  intro ψ₀
  obtain ⟨hm,hp,hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  refine ⟨hm,hp,?_⟩
  intro U hU ρ
  dsimp only
  rw [haarCardinalityBornScore_mean]
  exact radialWeyl_mean_trace_bounds (by omega) r _ _ lam h0 C₁ C₂ (haarPureVector ψ₀ U)
    (hc U hU) ρ

/-- The S error retains the original second radial coefficients and the same corrected columns. -/
theorem radialWeyl_auxiliary_matrix_error {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (C₁ C₂ : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (h : radialReadoutPolarControl d n r μ record lam localWeylFin 0 C₁ C₂ ψ) :
    ‖cardinalityReadoutAuxiliary d μ record r lam ((d:ℝ)^n) ψ.ofLp-
      radialWeylPolarMatrix r ψ * Matrix.diagonal
        (fun w : RadialWeylIndex d n r => (radialSecondCoefficient d r lam (weylWeight w.val):ℂ)) *
      (radialWeylPolarMatrix r ψ)ᴴ‖≤C₂*((n:ℝ)^3)⁻¹ := by
  have he := h.2.2.2.2
  change ‖rectangularEuclideanCLM _-rectangularEuclideanCLM _‖≤_ at he
  rw [← rectangularEuclideanCLM_sub,rectangularEuclideanCLM_norm] at he
  exact he

/-- The full M remainder and actual S approximation combine without treating S as a full second moment. -/
theorem radialWeyl_full_matrix_error {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (C₁ C₂ CM nu : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (h : radialReadoutPolarControl d n r μ record lam localWeylFin 0 C₁ C₂ ψ)
    (hM : ‖cardinalityReadoutSecond d μ record r lam ((d:ℝ)^n) ψ.ofLp-
      (nu • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)+
        cardinalityReadoutAuxiliary d μ record r lam ((d:ℝ)^n) ψ.ofLp)‖≤CM*((n:ℝ)^3)⁻¹) :
    ‖cardinalityReadoutSecond d μ record r lam ((d:ℝ)^n) ψ.ofLp-
      (nu • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)+
      radialWeylPolarMatrix r ψ * Matrix.diagonal
        (fun w : RadialWeylIndex d n r => (radialSecondCoefficient d r lam (weylWeight w.val):ℂ)) *
      (radialWeylPolarMatrix r ψ)ᴴ)‖≤(C₂+CM)*((n:ℝ)^3)⁻¹ := by
  have hs := radialWeyl_auxiliary_matrix_error r μ record lam C₁ C₂ ψ h
  have he (A B C D : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :
      A-(B+D)=(A-(B+C))+(C-D) := by abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hM hs).trans_eq (by ring))

end LocalCertification.Quantum
