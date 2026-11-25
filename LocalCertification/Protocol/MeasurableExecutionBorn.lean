import LocalCertification.Protocol.MeasurableExecutionFiltration
import LocalCertification.Quantum.MeasurablePOVMKernel
import LocalCertification.Quantum.Boundary

/-! Actual execution of a state-independent measurable POVM family.
This is the general physical executor. Admissibility of a local-product
measurement family is a separate physical restriction on the supplied family;
this file does not identify arbitrary global POVMs with local measurements. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory LocalCertification.Quantum
open LocalCertification.Information.KernelHistory
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u v
variable {Z S Ω : Type u} {I : Type v}
  [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I]

/-- Seed, rules, and original measurement family are fixed before the unknown
state. Only the induced Born law depends on that state. -/
structure BornProtocol (Z S Ω : Type u) (I : Type v)
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] extends RawProtocol Z S Ω where
  measurements : POVMKernel S Ω I

namespace BornProtocol
variable (P : BornProtocol Z S Ω I)

instance seedLaw_probability : IsProbabilityMeasure P.seedLaw := P.seed_probability

def kernel (ρ : QIT.State I) (m : ℕ) : Kernel (History Z Ω m) (Slot Ω) :=
  stoppedKernel P.toRawRules (P.measurements.bornKernel ρ) m

instance kernel_markov (ρ : QIT.State I) (m : ℕ) : IsMarkovKernel (P.kernel ρ m) := by
  unfold kernel
  infer_instance

theorem kernel_apply (ρ : QIT.State I) (m : ℕ) (h : History Z Ω m) :
    P.kernel ρ m h = match state P.toRawRules m h with
      | Sum.inl _ => Measure.dirac (Sum.inl ())
      | Sum.inr (_, s) => ((P.measurements.measurement s).born ρ).map Sum.inr :=
  stoppedKernel_apply P.toRawRules (P.measurements.bornKernel ρ) m h

def law (ρ : QIT.State I) : Measure (Sample Z (Slot Ω)) :=
  stoppedLaw P.toRawRules P.seedLaw (P.measurements.bornKernel ρ)

instance law_probability (ρ : QIT.State I) : IsProbabilityMeasure (P.law ρ) := by
  unfold law
  infer_instance

theorem law_prefix (ρ : QIT.State I) (m : ℕ) :
    (P.law ρ).map (rawPrefix m) = prefixLaw P.seedLaw (P.kernel ρ) m :=
  stoppedLaw_prefix P.toRawRules P.seedLaw (P.measurements.bornKernel ρ) m

theorem law_seed (ρ : QIT.State I) : (P.law ρ).map Prod.fst = P.seedLaw :=
  executionLaw_seed P.seedLaw (P.kernel ρ)

theorem law_ae_legal (ρ : QIT.State I) : ∀ᵐ p ∂P.law ρ, Legal P.toRawRules p :=
  stoppedLaw_ae_legal P.toRawRules P.seedLaw (P.measurements.bornKernel ρ)

def time : Sample Z (Slot Ω) → ℕ∞ := stoppingTime P.toRawRules
def reportedDecision : Sample Z (Slot Ω) → Fin 2 := terminalDecision P.toRawRules
def copyCost : Sample Z (Slot Ω) → ℝ≥0∞ := cost P.toRawRules

theorem time_measurable : Measurable P.time := stoppingTime_measurable P.toRawRules
theorem reportedDecision_measurable : Measurable P.reportedDecision := terminalDecision_measurable P.toRawRules
theorem copyCost_measurable : Measurable P.copyCost := cost_measurable P.toRawRules

def expectedCopies (ρ : QIT.State I) : ℝ≥0∞ := ∫⁻ p, P.copyCost p ∂P.law ρ

theorem expected_min (ρ : QIT.State I) (m : ℕ) :
    (∑ i ∈ Finset.range m, prefixLaw P.seedLaw (P.kernel ρ) i (active P.toRawRules i)) =
      ∫⁻ p, min (P.copyCost p) (m : ℝ≥0∞) ∂P.law ρ :=
  MeasurableExecution.expected_min P.toRawRules P.seedLaw (P.measurements.bornKernel ρ) m

theorem expected_truncations (ρ : QIT.State I) :
    (⨆ m : ℕ, ∫⁻ p, min (P.copyCost p) (m : ℝ≥0∞) ∂P.law ρ) = P.expectedCopies ρ :=
  MeasurableExecution.expected_truncations P.toRawRules (P.law ρ)

theorem prefixDecisionEvent_measure (ρ : QIT.State I) (j : Fin 2) (m : ℕ) :
    prefixLaw P.seedLaw (P.kernel ρ) m (MeasurableExecution.prefixDecisionEvent P.toRawRules j m) =
      P.law ρ (LocalCertification.Information.KernelTerminal.truncatedDecisionEvent
        P.time P.reportedDecision j m) :=
  MeasurableExecution.prefixDecisionEvent_measure P.toRawRules P.seedLaw (P.measurements.bornKernel ρ) j m

/-- Termination is evaluated separately in each actual input world. -/
def Terminates (ρ : QIT.State I) : Prop := ∀ᵐ p ∂P.law ρ, P.time p ≠ ⊤

/-- A physical cap quantifies over all legal seeds and original outcomes,
including branches of zero probability under every particular input. -/
def Capped (N : ℕ) : Prop := MeasurableExecution.Capped P.toRawRules N

theorem capped_terminates (N : ℕ) (h : P.Capped N) (ρ : QIT.State I) : P.Terminates ρ :=
  MeasurableExecution.capped_terminates P.toRawRules P.seedLaw (P.measurements.bornKernel ρ) N h

theorem capped_expectedCopies (N : ℕ) (h : P.Capped N) (ρ : QIT.State I) :
    P.expectedCopies ρ ≤ (N : ℝ≥0∞) :=
  capped_expected_cost P.toRawRules P.seedLaw (P.measurements.bornKernel ρ) N h

/-- Decision zero accepts high fidelity. Only promised inputs must terminate;
the actual common-seed/Born error and extended cost require no finite expectation. -/
def Valid (ψ : QIT.PureVector I) (a b δ : ℝ) : Prop :=
  (∀ ρ : QIT.State I, a ≤ pureTargetFidelity ψ ρ →
    P.Terminates ρ ∧ P.law ρ {p | P.reportedDecision p = 1} ≤ ENNReal.ofReal δ) ∧
  (∀ ρ : QIT.State I, pureTargetFidelity ψ ρ ≤ b →
    P.Terminates ρ ∧ P.law ρ {p | P.reportedDecision p = 0} ≤ ENNReal.ofReal δ)

end BornProtocol

/-- Full independently testable physical construction. All probability,
legality, exact-cost and finite-report facts follow from the actual Born kernel. -/
theorem exists_born_execution (P : RawProtocol Z S Ω) (M : POVMKernel S Ω I) :
    ∃ μ : QIT.State I → Measure (Sample Z (Slot Ω)),
      (∀ ρ, IsProbabilityMeasure (μ ρ)) ∧
      (∀ ρ n, (μ ρ).map (rawPrefix n) =
        prefixLaw P.seedLaw (stoppedKernel P.toRawRules (M.bornKernel ρ)) n) ∧
      (∀ ρ n h, stoppedKernel P.toRawRules (M.bornKernel ρ) n h =
        match state P.toRawRules n h with
        | Sum.inl _ => Measure.dirac (Sum.inl ())
        | Sum.inr (_, s) => ((M.measurement s).born ρ).map Sum.inr) ∧
      (∀ ρ, ∀ᵐ p ∂μ ρ, Legal P.toRawRules p) ∧
      (∀ ρ m, (∑ i ∈ Finset.range m,
          prefixLaw P.seedLaw (stoppedKernel P.toRawRules (M.bornKernel ρ)) i (active P.toRawRules i)) =
        ∫⁻ p, min (cost P.toRawRules p) (m : ℝ≥0∞) ∂μ ρ) ∧
      (∀ ρ j m, prefixLaw P.seedLaw (stoppedKernel P.toRawRules (M.bornKernel ρ)) m
          (prefixDecisionEvent P.toRawRules j m) =
        μ ρ (LocalCertification.Information.KernelTerminal.truncatedDecisionEvent
          (stoppingTime P.toRawRules) (terminalDecision P.toRawRules) j m)) ∧
      (∀ N, Capped P.toRawRules N → ∀ ρ,
        (∀ᵐ p ∂μ ρ, stoppingTime P.toRawRules p ≠ ⊤) ∧
        (∫⁻ p, cost P.toRawRules p ∂μ ρ) ≤ (N : ℝ≥0∞)) := by
  refine ⟨fun ρ => stoppedLaw P.toRawRules P.seedLaw (M.bornKernel ρ),
    fun _ => inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ n
    exact stoppedLaw_prefix P.toRawRules P.seedLaw (M.bornKernel ρ) n
  · intro ρ n h
    exact stoppedKernel_apply P.toRawRules (M.bornKernel ρ) n h
  · intro ρ
    exact stoppedLaw_ae_legal P.toRawRules P.seedLaw (M.bornKernel ρ)
  · intro ρ m
    exact expected_min P.toRawRules P.seedLaw (M.bornKernel ρ) m
  · intro ρ j m
    exact prefixDecisionEvent_measure P.toRawRules P.seedLaw (M.bornKernel ρ) j m
  · intro N h ρ
    exact ⟨capped_terminates P.toRawRules P.seedLaw (M.bornKernel ρ) N h,
      capped_expected_cost P.toRawRules P.seedLaw (M.bornKernel ρ) N h⟩

end LocalCertification.Protocol.MeasurableExecution
