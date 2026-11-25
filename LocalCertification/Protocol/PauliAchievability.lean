import LocalCertification.Protocol.RadialAchievability
import CertificationGaussian.ReadoutFullControl

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Probability
open scoped BigOperators ENNReal Matrix.Norms.L2Operator Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The actual finite-Pauli full-readout exceptional target set, under genuine global Haar sampling. -/
def pauliReadoutBad (n r : ℕ) (lam : ℕ → ℝ) (CM : ℝ)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1) : Set (ComplexUnitary (QuditIndex 2 n)) :=
  {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ₀∈
    radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam localWeylFin 0 CM}

/-- For every strict gamma window, the original finite three-Pauli-basis measurement score gives a genuine
raw protocol with K n^r log(1/delta) cost outside one explicit O(n^-8) target event.
The score coefficients, variance-spectrum bound, and exceptional-set constants are fixed before
a,b,delta,the initial target, and every unknown input state. -/
theorem pauli_achievability (r : ℕ) :
    ∃ (lam : ℕ → ℝ) (E CM Cbad : ℝ),0≤E ∧ 0<CM ∧ 0<Cbad ∧ lam 0=1 ∧
      admissible r (radialPolynomial 2 r lam) ∧
      envelopeRatio ((2:ℝ)+1) (radialPolynomial 2 r lam)=gamma ((2:ℝ)+1) r ∧
      ∀ a b : ℝ,a≤1 → 0≤b → b<1 → gamma ((2:ℝ)+1) r<(a-b)/(1-b) →
      ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
        ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
        MeasurableSet (pauliReadoutBad n r lam CM ψ₀) ∧
        complexUnitaryHaar (QuditIndex 2 n) (pauliReadoutBad n r lam CM ψ₀)≤
          ENNReal.ofReal (Cbad*((n:ℝ)^8)⁻¹) ∧
        ∀ U,U∉pauliReadoutBad n r lam CM ψ₀ → ∀ δ : ℝ,0<δ → δ≤1/2 →
          let ψ := haarPureVector ψ₀ U
          let l := lowerEnvelope ((2:ℝ)+1) (radialPolynomial 2 r lam)
          let u := upperEnvelope ((2:ℝ)+1) (radialPolynomial 2 r lam)
          let V := cardinalityReadoutTraceScale 2 n r (fun j => (lam j)^2)+E+1
          Valid (cardinalityMajorityProtocol pauliBasisUnitary continuous_of_discreteTopology (uniformFiniteOutcome 3)
            r lam ψ l u a b V δ) ψ a b δ ∧
          Capped (cardinalityMajorityProtocol pauliBasisUnitary continuous_of_discreteTopology (uniformFiniteOutcome 3)
            r lam ψ l u a b V δ) (blockCount δ*blockCopies V (scoreWindowGap l u a b)) ∧
          expectedBudget ψ a b δ≤ENat.toENNReal (maximumBudget ψ a b δ) ∧
          ENat.toENNReal (maximumBudget ψ a b δ)≤ENNReal.ofReal (K*(n:ℝ)^r*Real.log (1/δ)) := by
  have hd2 : 2≤(2:ℕ) := by norm_num
  obtain ⟨p,lam,hp,hpoly,h0,hr,_hl,_hu,_hc,hgap⟩ := optimal_radial_parameters 2 r hd2
  obtain ⟨E,hE,he⟩ := radialSecondCoefficient_bounded 2 r (by omega) lam
  obtain ⟨C₁,C₂,CM,_hC₁,_hC₂,hCM,hEvent⟩ := radialPauli_full_readout_haar_eventually
    r lam (0 : ZMod 2 × ZMod 2) localWeylLabel_card
  let Cbad := radialHighGaussianConstant 2 r lam+
    2*radialHighGaussianConstant 2 r (fun j => (lam j)^2)+3
  have hCbad : 0<Cbad := by
    have h₁ := radialHighGaussianConstant_pos 2 r hd2 lam
    have h₂ := radialHighGaussianConstant_pos 2 r hd2 (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  refine ⟨lam,E,CM,Cbad,hE.le,hCM,hCbad,h0,by rwa [hpoly],by rwa [hpoly],?_⟩
  intro a b ha hb0 hb1 hg
  have hΔ : 0<scoreWindowGap (lowerEnvelope ((2:ℝ)+1) (radialPolynomial 2 r lam))
      (upperEnvelope ((2:ℝ)+1) (radialPolynomial 2 r lam)) a b := by
    rw [hpoly]
    exact hgap a b hb1 hg
  obtain ⟨K,hK,hRun⟩ := radialWeyl_achievable_eventually hd2
    pauliBasisUnitary continuous_of_discreteTopology (uniformFiniteOutcome 3)
    r lam h0 C₁ C₂ CM E a b hE.le (fun w => (le_abs_self _).trans (he w)) ha hb0 hb1.le hΔ
  refine ⟨K,hK,?_⟩
  filter_upwards [hEvent,hRun] with n hE' hR
  intro ψ₀
  obtain ⟨hm,hp',hc⟩ := hE' localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  refine ⟨hm,hp',?_⟩
  intro U hU δ hδ hδhalf
  have hcontrol := hc U hU
  apply hR (haarPureVector ψ₀ U) hcontrol.1 _ δ hδ hδhalf
  have he := hcontrol.2.1
  simp only [cardinalityReadoutSecondError,sub_sub] at he
  rw [← Matrix.cstar_norm_def] at he
  exact he

end LocalCertification.Protocol
