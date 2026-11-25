import LocalCertification.Protocol.MeasurableExecutionBorn
import LocalCertification.Protocol.MeasurableExecutionLegacy
import LocalCertification.Quantum.MeasurablePOVMBasis

/-! Embed the actual existing product-basis protocol in the general physical
executor. This changes only padded-label representation and preserves the
original seed, rules, local product measurements, full laws and budgets. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
variable {Z : Type} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

def basisProtocol (P : QuditProtocol Z d n) :
    BornProtocol Z (ProductSetting d n) (CertificationGaussian.QuditIndex d n)
      (CertificationGaussian.QuditIndex d n) where
  toRawProtocol := P
  measurements := POVMKernel.productBasis d n

theorem basisProtocol_law (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (basisProtocol P).law ρ = (Protocol.executionLaw P ρ).map Legacy.sampleEquiv := by
  change stoppedLaw P.toRawRules P.seedLaw ((POVMKernel.productBasis d n).bornKernel ρ) = _
  simp only [POVMKernel.bornKernel_productBasis]
  exact Legacy.stoppedLaw_conjugacy P.toRawRules P.seedLaw (productBornKernel d n ρ)

theorem basisProtocol_time (P : QuditProtocol Z d n) (p : RawSample Z (CertificationGaussian.QuditIndex d n))
    (hp : ∀ m, ConsistentPrefix P.toRawRules m (Protocol.rawPrefix m p)) :
    (basisProtocol P).time (Legacy.sampleEquiv p) = Protocol.executionTime P p :=
  Legacy.stoppingTime_sampleEquiv P.toRawRules p hp

theorem basisProtocol_decision (P : QuditProtocol Z d n) (p : RawSample Z (CertificationGaussian.QuditIndex d n))
    (hp : ∀ m, ConsistentPrefix P.toRawRules m (Protocol.rawPrefix m p)) :
    (basisProtocol P).reportedDecision (Legacy.sampleEquiv p) = Protocol.executionDecision P p :=
  Legacy.terminalDecision_sampleEquiv P.toRawRules p hp

theorem basisProtocol_expectedCopies (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (basisProtocol P).expectedCopies ρ = Protocol.expectedCopies P ρ := by
  rw [BornProtocol.expectedCopies, basisProtocol_law,
    lintegral_map (basisProtocol P).copyCost_measurable Legacy.sampleEquiv.measurable]
  apply lintegral_congr_ae
  filter_upwards [Protocol.executionLaw_ae_consistent P ρ] with p hp
  exact congrArg ENat.toENNReal (basisProtocol_time P p hp)

theorem basisProtocol_terminates_iff (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (basisProtocol P).Terminates ρ ↔ Protocol.Terminates P ρ := by
  unfold BornProtocol.Terminates Protocol.Terminates
  rw [basisProtocol_law]
  have hm : MeasurableSet {p | (basisProtocol P).time p ≠ ⊤} :=
    ((basisProtocol P).time_measurable (measurableSet_singleton ⊤)).compl
  rw [ae_map_iff Legacy.sampleEquiv.measurable.aemeasurable hm]
  apply Filter.eventually_congr
  filter_upwards [Protocol.executionLaw_ae_consistent P ρ] with p hp
  rw [basisProtocol_time P p hp]
  rfl

theorem basisProtocol_decision_measure (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : Fin 2) :
    (basisProtocol P).law ρ {p | (basisProtocol P).reportedDecision p = j} =
      Protocol.executionLaw P ρ {p | Protocol.executionDecision P p = j} := by
  have hm : MeasurableSet {p | (basisProtocol P).reportedDecision p = j} :=
    (basisProtocol P).reportedDecision_measurable (measurableSet_singleton j)
  rw [basisProtocol_law, Measure.map_apply Legacy.sampleEquiv.measurable hm]
  apply measure_congr
  filter_upwards [Protocol.executionLaw_ae_consistent P ρ] with p hp
  apply propext
  change (basisProtocol P).reportedDecision (Legacy.sampleEquiv p) = j ↔ Protocol.executionDecision P p = j
  rw [basisProtocol_decision P p hp]

theorem basisProtocol_valid_iff (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    (basisProtocol P).Valid ψ a b δ ↔ Protocol.Valid P ψ a b δ := by
  unfold BornProtocol.Valid Protocol.Valid
  simp only [basisProtocol_terminates_iff, basisProtocol_decision_measure]

theorem basisProtocol_capped_iff (P : QuditProtocol Z d n) (N : ℕ) :
    (basisProtocol P).Capped N ↔ Protocol.Capped P N := Legacy.capped_iff P.toRawRules N

theorem exists_basis_embedding (P : QuditProtocol Z d n) :
    ∃ Q : BornProtocol Z (ProductSetting d n)
        (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n),
      Q.toRawProtocol = P ∧
      Q.measurements = POVMKernel.productBasis d n ∧
      (∀ ρ, Q.law ρ = (Protocol.executionLaw P ρ).map Legacy.sampleEquiv) ∧
      (∀ ρ, Q.expectedCopies ρ = Protocol.expectedCopies P ρ) ∧
      (∀ ψ a b δ, Q.Valid ψ a b δ ↔ Protocol.Valid P ψ a b δ) ∧
      (∀ N, Q.Capped N ↔ Protocol.Capped P N) :=
  ⟨basisProtocol P, rfl, rfl, basisProtocol_law P, basisProtocol_expectedCopies P,
    basisProtocol_valid_iff P, basisProtocol_capped_iff P⟩

end LocalCertification.Protocol.MeasurableExecution
