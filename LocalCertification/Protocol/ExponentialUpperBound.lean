import LocalCertification.Protocol.LinearAchievability

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Probability
open scoped BigOperators ENNReal Matrix.Norms.L2Operator Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The actual full-readout exceptional target set, under genuine global Haar sampling. -/
def linearHaarReadoutBad (d n r : ℕ) [NeZero d] (ε : ℝ) (lam : ℕ → ℝ) (CM : ℝ)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) : Set (ComplexUnitary (QuditIndex d n)) :=
  {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀∈
    radialLinearReadoutFullBad d n r ε (haarBasisRecords d) id lam localWeylFin 0 CM}

/-- For every strict gamma window, the original full-Haar local measurement score gives a genuine
raw protocol with K n^r log(1/delta) cost outside one explicit exponentially small target event.
The score coefficients, variance-spectrum bound, and exceptional-set constants are fixed before
a,b,delta,the initial target, and every unknown input state. -/
theorem haar_achievability_exponential (d r : ℕ) (hd : 3≤d) [NeZero d] :
    ∃ (lam : ℕ → ℝ) (ε E CM c : ℝ),0<ε ∧ 0≤E ∧ 0<CM ∧ 0<c ∧ lam 0=1 ∧
      admissible r (radialPolynomial d r lam) ∧
      envelopeRatio ((d:ℝ)+1) (radialPolynomial d r lam)=gamma ((d:ℝ)+1) r ∧
      ∀ a b : ℝ,a≤1 → 0≤b → b<1 → gamma ((d:ℝ)+1) r<(a-b)/(1-b) →
      ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
        ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
        MeasurableSet (linearHaarReadoutBad d n r ε lam CM ψ₀) ∧
        complexUnitaryHaar (QuditIndex d n) (linearHaarReadoutBad d n r ε lam CM ψ₀)≤
          ENNReal.ofReal (Real.exp (-c*n)) ∧
        ∀ U,U∉linearHaarReadoutBad d n r ε lam CM ψ₀ → ∀ δ : ℝ,0<δ → δ≤1/2 →
          let ψ := haarPureVector ψ₀ U
          let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
          let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
          let V := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)+E+1
          Valid (cardinalityMajorityProtocol id continuous_id (complexUnitaryHaar (Fin d))
            r lam ψ l u a b V δ) ψ a b δ ∧
          Capped (cardinalityMajorityProtocol id continuous_id (complexUnitaryHaar (Fin d))
            r lam ψ l u a b V δ) (blockCount δ*blockCopies V (scoreWindowGap l u a b)) ∧
          expectedBudget ψ a b δ≤ENat.toENNReal (maximumBudget ψ a b δ) ∧
          ENat.toENNReal (maximumBudget ψ a b δ)≤ENNReal.ofReal (K*(n:ℝ)^r*Real.log (1/δ)) := by
  have hd2 : 2≤d := by omega
  obtain ⟨p,lam,hp,hpoly,h0,hr,_hl,_hu,_hc,hgap⟩ := optimal_radial_parameters d r hd2
  obtain ⟨E,hE,he⟩ := radialSecondCoefficient_bounded d r (by omega) lam
  obtain ⟨ε,c,C₁,C₂,CM,hε,_hhalf,_hentropy,hc,_hC₁,_hC₂,hCM,hEvent⟩ :=
    radialHaar_readout_exponential d r hd lam (0 : ZMod d × ZMod d) localWeylLabel_card
  refine ⟨lam,ε,E,CM,c,hε,hE.le,hCM,hc,h0,by rwa [hpoly],by rwa [hpoly],?_⟩
  intro a b ha hb0 hb1 hg
  have hΔ : 0<scoreWindowGap (lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
      (upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)) a b := by
    rw [hpoly]
    exact hgap a b hb1 hg
  obtain ⟨K,hK,hRun⟩ := linearWeyl_achievable_eventually hd2
    (id : LocalUnitary d → LocalUnitary d) continuous_id (complexUnitaryHaar (Fin d))
    r ε lam h0 C₁ C₂ CM E a b hE.le (fun w => (le_abs_self _).trans (he w)) ha hb0 hb1.le hΔ
  refine ⟨K,hK,?_⟩
  filter_upwards [hEvent,hRun] with n hE' hR
  intro ψ₀
  obtain ⟨hm,hp',hc⟩ := hE' localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  refine ⟨hm,hp',?_⟩
  intro U hU δ hδ hδhalf
  have hcontrol := hc U hU
  exact hR (haarPureVector ψ₀ U) hcontrol δ hδ hδhalf

/-- The actual finite-Pauli full-readout exceptional target set, under genuine global Haar sampling. -/
def linearPauliReadoutBad (n r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (CM : ℝ)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1) : Set (ComplexUnitary (QuditIndex 2 n)) :=
  {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ₀∈
    radialLinearReadoutFullBad 2 n r ε pauliBasisRecords pauliFullRecord lam localWeylFin 0 CM}

/-- For every strict gamma window, the original finite three-Pauli-basis measurement score gives a genuine
raw protocol with K n^r log(1/delta) cost outside one explicit exponentially small target event.
The score coefficients, variance-spectrum bound, and exceptional-set constants are fixed before
a,b,delta,the initial target, and every unknown input state. -/
theorem pauli_achievability_exponential (r : ℕ) :
    ∃ (lam : ℕ → ℝ) (ε E CM c : ℝ),0<ε ∧ 0≤E ∧ 0<CM ∧ 0<c ∧ lam 0=1 ∧
      admissible r (radialPolynomial 2 r lam) ∧
      envelopeRatio ((2:ℝ)+1) (radialPolynomial 2 r lam)=gamma ((2:ℝ)+1) r ∧
      ∀ a b : ℝ,a≤1 → 0≤b → b<1 → gamma ((2:ℝ)+1) r<(a-b)/(1-b) →
      ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
        ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
        MeasurableSet (linearPauliReadoutBad n r ε lam CM ψ₀) ∧
        complexUnitaryHaar (QuditIndex 2 n) (linearPauliReadoutBad n r ε lam CM ψ₀)≤
          ENNReal.ofReal (Real.exp (-c*n)) ∧
        ∀ U,U∉linearPauliReadoutBad n r ε lam CM ψ₀ → ∀ δ : ℝ,0<δ → δ≤1/2 →
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
  obtain ⟨ε,c,C₁,C₂,CM,hε,_hhalf,_hentropy,hc,_hC₁,_hC₂,hCM,hEvent⟩ :=
    radialPauli_readout_exponential r lam (0 : ZMod 2 × ZMod 2) localWeylLabel_card
  refine ⟨lam,ε,E,CM,c,hε,hE.le,hCM,hc,h0,by rwa [hpoly],by rwa [hpoly],?_⟩
  intro a b ha hb0 hb1 hg
  have hΔ : 0<scoreWindowGap (lowerEnvelope ((2:ℝ)+1) (radialPolynomial 2 r lam))
      (upperEnvelope ((2:ℝ)+1) (radialPolynomial 2 r lam)) a b := by
    rw [hpoly]
    exact hgap a b hb1 hg
  obtain ⟨K,hK,hRun⟩ := linearWeyl_achievable_eventually hd2
    pauliBasisUnitary continuous_of_discreteTopology (uniformFiniteOutcome 3)
    r ε lam h0 C₁ C₂ CM E a b hE.le (fun w => (le_abs_self _).trans (he w)) ha hb0 hb1.le hΔ
  refine ⟨K,hK,?_⟩
  filter_upwards [hEvent,hRun] with n hE' hR
  intro ψ₀
  obtain ⟨hm,hp',hc⟩ := hE' localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  refine ⟨hm,hp',?_⟩
  intro U hU δ hδ hδhalf
  have hcontrol := hc U hU
  exact hR (haarPureVector ψ₀ U) hcontrol δ hδ hδhalf

/-- The actual all-d upper budget with one exponentially small exceptional set and all delta together. -/
theorem qudit_budget_upper_exponential (d r : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (ha : a≤1) (hb0 : 0≤b) (hb1 : b<1)
    (hg : gamma ((d:ℝ)+1) r<(a-b)/(1-b)) :
    ∃ K c : ℝ,0<K ∧ 0<c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (Real.exp (-c*n)) ∧
        ∀ U,U∉bad → ∀ δ : ℝ,0<δ → δ≤1/2 →
          expectedBudget (haarPureVector ψ₀ U) a b δ≤ENat.toENNReal (maximumBudget (haarPureVector ψ₀ U) a b δ) ∧
          ENat.toENNReal (maximumBudget (haarPureVector ψ₀ U) a b δ)≤
            ENNReal.ofReal (K*(n:ℝ)^r*Real.log (1/δ)) := by
  by_cases hd2 : d=2
  · subst d
    obtain ⟨lam,ε,E,CM,c,_hε,_hE,_hCM,hc,_h0,_hp,_hr,hall⟩ := pauli_achievability_exponential r
    obtain ⟨K,hK,hN⟩ := hall a b ha hb0 hb1 hg
    refine ⟨K,c,hK,hc,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    obtain ⟨hm,hprob,hvalid⟩ := hn ψ₀
    refine ⟨linearPauliReadoutBad n r ε lam CM ψ₀,hm,hprob,?_⟩
    intro U hU δ hδ hhalf
    exact (hvalid U hU δ hδ hhalf).2.2
  · have hd3 : 3≤d := by omega
    obtain ⟨lam,ε,E,CM,c,_hε,_hE,_hCM,hc,_h0,_hp,_hr,hall⟩ := haar_achievability_exponential d r hd3
    obtain ⟨K,hK,hN⟩ := hall a b ha hb0 hb1 hg
    refine ⟨K,c,hK,hc,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    obtain ⟨hm,hprob,hvalid⟩ := hn ψ₀
    refine ⟨linearHaarReadoutBad d n r ε lam CM ψ₀,hm,hprob,?_⟩
    intro U hU δ hδ hhalf
    exact (hvalid U hU δ hδ hhalf).2.2

end LocalCertification.Protocol
