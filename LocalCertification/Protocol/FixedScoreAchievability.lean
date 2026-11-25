import LocalCertification.Protocol.RadialAchievability
import LocalCertification.Quantum.CompleteReadoutLoewner

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Probability
open scoped BigOperators ENNReal Matrix.Norms.L2Operator Topology
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {H : Type u} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]
  [CompactSpace H] [SecondCountableTopology H] {d n : ℕ} [NeZero d]

/-- The actual implemented score protocol and its original explicit 1548 V/Delta² logarithmic budget.
This records conclusions about the raw protocol, not an interface assumption supplying a test. -/
def FixedScoreAchievable (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ)
    (E a b δ : ℝ) (ψ : QIT.PureVector (QuditIndex d n)) : Prop :=
  let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let V := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)+E+1
  Valid (cardinalityMajorityProtocol setting hs ν r lam ψ l u a b V δ) ψ a b δ ∧
  Capped (cardinalityMajorityProtocol setting hs ν r lam ψ l u a b V δ)
    (blockCount δ*blockCopies V (scoreWindowGap l u a b)) ∧
  expectedBudget ψ a b δ≤ENat.toENNReal (maximumBudget ψ a b δ) ∧
  ENat.toENNReal (maximumBudget ψ a b δ)≤
    ENNReal.ofReal (1548*V/(scoreWindowGap l u a b)^2*Real.log (1/δ))

/-- The full original operator event yields the exact finite-size score budget for arbitrary signed
fixed coefficients. The dimension cutoff precedes the target and every requested error. -/
theorem fixedScore_achievable_of_full_control_eventually (hd : 2≤d)
    (setting : H → LocalUnitary d) (hs : Continuous setting) (ν : Measure H) [IsProbabilityMeasure ν]
    (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0=1) (C₁ C₂ CM E a b : ℝ)
    (hE : 0≤E) (he : ∀ w : ℕ,radialSecondCoefficient d r lam w≤E)
    (ha : a≤1) (hb0 : 0≤b) (hb1 : b≤1)
    (hg : 0<scoreWindowGap (lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
      (upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)) a b) :
    ∀ᶠ n : ℕ in atTop,∀ ψ : QIT.PureVector (QuditIndex d n),
      radialReadoutFullControl d n r (ν.prod (uniformFiniteOutcome d))
        (fun p : H × Fin d => (setting p.1,p.2)) lam localWeylFin 0 C₁ C₂ CM (WithLp.toLp 2 ψ.amp) →
      ∀ δ : ℝ,0<δ → δ≤1/2 → FixedScoreAchievable setting hs ν r lam E a b δ ψ := by
  let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let Δ := scoreWindowGap l u a b
  filter_upwards [eventually_inverse_cube_error (C₁+2*|1-l|) (Δ/4) (by positivity),
    eventually_inverse_cube_error (C₁+2*|1-u|) (Δ/4) (by positivity),
    eventually_inverse_cube_error (C₂+CM) 1 (by norm_num)] with n hL hU hM
  intro ψ hfullcontrol δ hδ hδhalf
  have hcontrol := hfullcontrol.1
  have hrem := hfullcontrol.2.1
  simp only [cardinalityReadoutSecondError,sub_sub] at hrem
  rw [← Matrix.cstar_norm_def] at hrem
  let Q := radialWeylPolarMatrix r (WithLp.toLp 2 ψ.amp)
  let c : RadialWeylIndex d n r → ℝ := fun w => radialFirstCoefficient d r lam (weylWeight w.val)
  let e : RadialWeylIndex d n r → ℝ := fun w => radialSecondCoefficient d r lam (weylWeight w.val)
  let nu := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)
  have hq : 1<(d:ℝ)+1 := by
    have : (2:ℝ)≤d := by exact_mod_cast hd
    linarith
  have hc := radialWeyl_coefficients (d:=d) (n:=n) r lam h0 (by omega)
  have hL' : C₁*((n:ℝ)^3)⁻¹+|1-l| *(2*((n:ℝ)^3)⁻¹)≤Δ/4 := by nlinarith [hL]
  have hU' : C₁*((n:ℝ)^3)⁻¹+|1-u| *(2*((n:ℝ)^3)⁻¹)≤Δ/4 := by nlinarith [hU]
  let μ := ν.prod (uniformFiniteOutcome d)
  let record : H × Fin d → ComplexUnitary (Fin d) × Fin d := fun p => (setting p.1,p.2)
  let ψv : EuclideanSpace ℂ (QuditIndex d n) := WithLp.toLp 2 ψ.amp
  have hB := radialWeyl_first_matrix_error (d:=d) (n:=n) r μ record lam C₁ C₂ ψv hcontrol
  have hfull := radialWeyl_full_matrix_error (d:=d) (n:=n) r μ record lam C₁ C₂ CM nu ψv hcontrol hrem
  have hP := radialWeyl_target_projector (d:=d) (n:=n) r μ record lam C₁ C₂ ψ hcontrol
  have hr := cardinality_achievable_of_spectral_control (d:=d) (n:=n) (J:=RadialWeylIndex d n r) setting hs ν r lam ψ Q hcontrol.1
    (radialWeylIdentity d n r) c e hc.1 l u E nu (C₁*((n:ℝ)^3)⁻¹)
    ((C₂+CM)*((n:ℝ)^3)⁻¹) (2*((n:ℝ)^3)⁻¹) a b δ
    (envelope_zero_bounds _ hq _).1 (envelope_zero_bounds _ hq _).2 hE
    (squared_traceScale_nonneg d n r (by omega) lam)
    (fun w hw => (hc.2 w hw).1) (fun w hw => (hc.2 w hw).2) (fun w => he _)
    hB hfull hP
    ha hb0 hb1 hg hL' hU' hM hδ hδhalf
  exact hr

end LocalCertification.Protocol
