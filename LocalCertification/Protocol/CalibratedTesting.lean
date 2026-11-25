import LocalCertification.Protocol.TerminalInformation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter Metric LocalCertification.Information LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal LocalCertification.Information Topology
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]

/-- The actual calibrated pair is used in its proved parity direction, including the critical window equality. -/
theorem calibrated_terminal_information (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (a b δ : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (hgap : (a-b)/(1-b) ≤ gamma ((d : ℝ)+1) r)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2) (P : QuditProtocol Z d n) (hv : Valid P ψ a b δ)
    (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
      (productBornMeasure d n U (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤ L) :
    ENNReal.ofReal (testingThreshold δ) ≤
      L * expectedCopies P (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb) := by
  obtain ⟨hlo,hhi⟩ := calibrated_exact_window hd r ψ hN a b hb0 hb1 hlb hgap
  dsimp only [calibratedNumeratorState, calibratedDenominatorState] at hL ⊢
  by_cases hr : Even r
  · simp only [ite_eq_left hr] at hL ⊢
    exact valid_information_low_high P ψ a b δ hv hδ hhalf _ _ hlo.le hhi L hL
  · simp only [ite_eq_right hr] at hL ⊢
    exact valid_information_high_low P ψ a b δ hv hδ hhalf _ _ hhi hlo.le L hL

/-- A direct consumer of the actual common Haar event, without a supplied information-bound hypothesis. -/
theorem calibratedHaarGoodEvent_terminal (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (C : ℝ)
    (W : CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n))
    (hW : W ∈ dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n)) (hn : 1 ≤ n)
    (a b δ : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r (haarPureVector ψ W) hN < b)
    (hgap : (a-b)/(1-b) ≤ gamma ((d : ℝ)+1) r)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2) (P : QuditProtocol Z d n)
    (hv : Valid P (haarPureVector ψ W) a b δ) :
    ENNReal.ofReal (testingThreshold δ) ≤
      ENNReal.ofReal (2*calibratedUniformWeight hd r b*(1+C/n)*
        CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r)) +
        (4/calibratedUniformWeight hd r b)*((n : ℝ)^6/(d : ℝ)^n)) *
      expectedCopies P (calibratedNumeratorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb) :=
  calibrated_terminal_information hd r _ hN a b δ hb0 hb1 hlb hgap hδ hhalf P hv _
    (calibratedHaarGoodEvent_klDiv hd r ψ hN C W hW hn b hb0 hb1 hlb)

/-- Division is used only for a strictly positive finite coefficient; the expected cost may be infinite. -/
theorem expected_cost_power_lower (K B : ℝ) (hK : 0 < K) (n r : ℕ) (hn : 1 ≤ n)
    (E : ℝ≥0∞) (h : ENNReal.ofReal B ≤ ENNReal.ofReal (K/(n : ℝ)^(r+1)) * E) :
    ENNReal.ofReal ((B/K)*(n : ℝ)^(r+1)) ≤ E := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hc : 0 < K/(n : ℝ)^(r+1) := div_pos hK (pow_pos hnR _)
  have hdiv := (ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top).mpr h
  rw [← ENNReal.ofReal_div_of_pos hc] at hdiv
  have he : B/(K/(n : ℝ)^(r+1)) = (B/K)*(n : ℝ)^(r+1) := by field_simp
  rwa [he] at hdiv

omit [MeasurableSpace Z] in
/-- Uniform actual-protocol lower bound on one measurable Haar target event.
Constants and the event are fixed before the error, promise threshold, seed space's protocol,
and its adaptive choices; the concrete witness state is a promised calibrated physical input. -/
theorem calibratedHaar_expected_lower (hd : 2 ≤ d) (r : ℕ) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      MeasurableSet (dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n)) ∧
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
          (dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n))ᶜ ≤
        ENNReal.ofReal (((r+1 : ℕ) : ℝ)/(n : ℝ)^3)+ENNReal.ofReal (Real.exp (-c*(n : ℝ)^3)) ∧
      ∀ W ∈ dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n),
        ∃ hlb : uncalibratedLowFidelity hd r (haarPureVector ψ W) hN < b,
        ∀ a δ : ℝ, (a-b)/(1-b) ≤ gamma ((d : ℝ)+1) r → 0 < δ → δ < 1 / 2 →
        ∀ (Z : Type u) [MeasurableSpace Z], ∀ P : QuditProtocol Z d n, Valid P (haarPureVector ψ W) a b δ →
          ENNReal.ofReal ((testingThreshold δ/K)*(n : ℝ)^(r+1)) ≤
            expectedCopies P (calibratedNumeratorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb) := by
  obtain ⟨c,C,K,hc,hC,hK,N,hgood⟩ := calibratedHaar_hard_states hd r b hb0 hb1
  refine ⟨c,C,K,hc,hC,hK,max N 1,?_⟩
  intro n hn ψ
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hN,hm,hprob,hpair⟩ := hgood n hnN ψ
  refine ⟨hN,hm,hprob,?_⟩
  intro W hW
  obtain ⟨hlb,_,_,hL⟩ := hpair W hW
  refine ⟨hlb,?_⟩
  intro a δ hgap hδ hhalf Z _ P hv
  exact expected_cost_power_lower K (testingThreshold δ) hK n r hn1 _
    (calibrated_terminal_information hd r _ hN a b δ hb0 hb1 hlb hgap hδ hhalf P hv _ hL)

/-- Any genuine every-path cap dominates each actual expected input cost, hence any proved lower bound. -/
theorem capped_budget_lower (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (B : ℝ≥0∞) (hB : B ≤ expectedCopies P ρ) (M : ℕ) (hM : Capped P M) : B ≤ (M : ℝ≥0∞) :=
  hB.trans (expectedCopies_le_of_capped P M hM ρ)

end LocalCertification.Protocol
