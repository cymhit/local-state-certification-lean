import LocalCertification.Protocol.Budgets
import LocalCertification.Protocol.CalibratedTesting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Metric LocalCertification.Information LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
variable {d n : ℕ} [NeZero d]

/-- The parity-selected actual source of the information inequality is one of the promised physical states. -/
theorem calibratedNumerator_promised (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (a b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (hgap : (a-b)/(1-b) ≤ gamma ((d : ℝ)+1) r) :
    calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb ∈ promisedStates ψ a b := by
  obtain ⟨hlo,hhi⟩ := calibrated_exact_window hd r ψ hN a b hb0 hb1 hlb hgap
  dsimp only [promisedStates, Set.mem_ofPred_eq, calibratedNumeratorState]
  split_ifs
  · exact Or.inr hlo.le
  · exact Or.inl hhi

/-- Both formal budgets inherit the actual-protocol lower bound on one common measurable Haar target event.
The maximum budget is the least feasible natural cap, the expected budget is an extended infimum;
all original seed universes are covered by the proved full-image normalization. -/
theorem calibratedHaar_budget_lower (hd : 2 ≤ d) (r : ℕ) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      MeasurableSet (dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n)) ∧
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
          (dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n))ᶜ ≤
        ENNReal.ofReal (((r+1 : ℕ) : ℝ)/(n : ℝ)^3)+ENNReal.ofReal (Real.exp (-c*(n : ℝ)^3)) ∧
      ∀ W ∈ dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n),
        ∀ a δ : ℝ, (a-b)/(1-b) ≤ gamma ((d : ℝ)+1) r → 0 < δ → δ < 1 / 2 →
          ENNReal.ofReal ((testingThreshold δ/K)*(n : ℝ)^(r+1)) ≤
            expectedBudget (haarPureVector ψ W) a b δ ∧
          ENNReal.ofReal ((testingThreshold δ/K)*(n : ℝ)^(r+1)) ≤
            ENat.toENNReal (maximumBudget (haarPureVector ψ W) a b δ) := by
  obtain ⟨c,C,K,hc,hC,hK,N,hgood⟩ := calibratedHaar_expected_lower.{0} hd r b hb0 hb1
  refine ⟨c,C,K,hc,hC,hK,N,?_⟩
  intro n hn ψ
  obtain ⟨hN,hm,hprob,hbound⟩ := hgood n hn ψ
  refine ⟨hN,hm,hprob,?_⟩
  intro W hW a δ hgap hδ hhalf
  obtain ⟨hlb,hall⟩ := hbound W hW
  have hpromise := calibratedNumerator_promised hd r (haarPureVector ψ W) hN a b hb0 hb1 hlb hgap
  have he : ENNReal.ofReal ((testingThreshold δ/K)*(n : ℝ)^(r+1)) ≤
      expectedBudget (haarPureVector ψ W) a b δ := by
    apply expectedBudget_lower
    intro Q hv
    exact (hall a δ hgap hδ hhalf Q.1 Q.toRaw hv).trans
      (expectedCopies_le_protocolCost Q.toRaw (haarPureVector ψ W) a b _ hpromise)
  exact ⟨he, he.trans (expectedBudget_le_maximumBudget (haarPureVector ψ W) a b δ)⟩

end LocalCertification.Protocol
