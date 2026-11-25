import LocalCertification.Protocol.TerminalEvents
import LocalCertification.Information.BinarySupport

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information Topology
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- Terminal testing follows from the true finite-prefix bounds and two separate termination laws.
The multiplier and cost remain extended-valued; no finite-entropy or finite-expectation premise is added. -/
theorem terminal_binary_information (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) (δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (hp : 1 - δ ≤ (executionLaw P ρ).real {p | executionDecision P p = j})
    (hq : (executionLaw P σ).real {p | executionDecision P p = j} ≤ δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  let t := Real.log ((1 - δ) / δ)
  have hpair := (prefixDecisionEvent_probability_tendsto P ρ hρ j).prodMk_nhds
    (prefixDecisionEvent_probability_tendsto P σ hσ j)
  have hlim := ((ENNReal.continuous_ofReal.comp (binarySupport_continuous t)).tendsto
    ((executionLaw P ρ).real {p | executionDecision P p = j},
      (executionLaw P σ).real {p | executionDecision P p = j})).comp hpair
  have hbound (m : ℕ) : ENNReal.ofReal (binarySupport t
      ((executionPrefixLaw P ρ m).real (prefixDecisionEvent P j m))
      ((executionPrefixLaw P σ m).real (prefixDecisionEvent P j m))) ≤ L * expectedCopies P ρ :=
    (binarySupport_le_klDiv (executionPrefixLaw P ρ m) (executionPrefixLaw P σ m)
      (prefixDecisionEvent P j m) (prefixDecisionEvent_measurable P j m) t).trans
        (execution_klDiv_le_expected P ρ σ L hL m)
  exact (ENNReal.ofReal_le_ofReal (testingThreshold_le_binarySupport δ _ _ hδ hhalf hp hq)).trans
    (le_of_tendsto hlim (Filter.Eventually.of_forall hbound))

/-- The source rejects j with probability at most δ, while the target accepts j with probability at most δ. -/
theorem terminal_information_of_errors (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) (δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (hsource : executionLaw P ρ {p | executionDecision P p ≠ j} ≤ ENNReal.ofReal δ)
    (htarget : executionLaw P σ {p | executionDecision P p = j} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsource
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top htarget
  rw [ENNReal.toReal_ofReal hδ.le] at he ht
  have hc := probReal_compl_eq_one_sub (μ := executionLaw P ρ)
    ((executionDecision_measurable P) (measurableSet_singleton j))
  change (executionLaw P ρ).real ({p | executionDecision P p = j}ᶜ) =
    1 - (executionLaw P ρ).real {p | executionDecision P p = j} at hc
  have hp : 1 - δ ≤ (executionLaw P ρ).real {p | executionDecision P p = j} := by
    change (executionLaw P ρ).real ({p | executionDecision P p = j}ᶜ) ≤ δ at he
    rw [hc] at he
    linarith
  exact terminal_binary_information P ρ σ L hL hρ hσ j δ hδ hhalf hp ht

/-- For high-to-low KL, decision 0 accepts the source; this does not exchange the KL arguments. -/
theorem valid_information_high_low (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hvalid : Valid P ψ a b δ) (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hhigh : a ≤ pureTargetFidelity ψ ρ) (hlow : pureTargetFidelity ψ σ ≤ b)
    (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  obtain ⟨hρ, heρ⟩ := hvalid.1 ρ hhigh
  obtain ⟨hσ, heσ⟩ := hvalid.2 σ hlow
  have he : {p | executionDecision P p ≠ 0} = {p | executionDecision P p = 1} := by
    ext p
    have hj : executionDecision P p = 0 ∨ executionDecision P p = 1 := by omega
    rcases hj with hj | hj <;> simp [hj]
  apply terminal_information_of_errors P ρ σ L hL hρ hσ 0 δ hδ hhalf
  · rw [he]
    exact heρ
  · exact heσ

/-- For low-to-high KL, decision 1 accepts the source, preserving the physical parity-selected direction. -/
theorem valid_information_low_high (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hvalid : Valid P ψ a b δ) (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hlow : pureTargetFidelity ψ ρ ≤ b) (hhigh : a ≤ pureTargetFidelity ψ σ)
    (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  obtain ⟨hρ, heρ⟩ := hvalid.2 ρ hlow
  obtain ⟨hσ, heσ⟩ := hvalid.1 σ hhigh
  have he : {p | executionDecision P p ≠ 1} = {p | executionDecision P p = 0} := by
    ext p
    have hj : executionDecision P p = 0 ∨ executionDecision P p = 1 := by omega
    rcases hj with hj | hj <;> simp [hj]
  apply terminal_information_of_errors P ρ σ L hL hρ hσ 1 δ hδ hhalf
  · rw [he]
    exact heρ
  · exact heσ

end LocalCertification.Protocol
