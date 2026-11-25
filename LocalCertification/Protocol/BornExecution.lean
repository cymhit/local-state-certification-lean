import LocalCertification.Protocol.ConsistentHistory
import LocalCertification.Quantum.FiniteBornInformation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u

/-- The whole product setting, selected once before measuring a copy. -/
abbrev ProductSetting (d n : ℕ) := Fin n → CertificationGaussian.LocalUnitary d

/-- Raw qudit protocols retain arbitrary measurable seeds and the actual full quantum outcome alphabet. -/
abbrev QuditProtocol (Z : Type u) [MeasurableSpace Z] (d n : ℕ) :=
  RawProtocol Z (ProductSetting d n) (CertificationGaussian.QuditIndex d n)

variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]

local instance executionOutcomeInhabited : Inhabited (CertificationGaussian.QuditIndex d n) :=
  ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
local instance executionSettingInhabited : Inhabited (ProductSetting d n) := ⟨fun _ => 1⟩

/-- The input state determines only the physical Born draws, never the common seed or original rules. -/
def executionPrefixLaw (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    Measure (SlotHistory Z (CertificationGaussian.QuditIndex d n) m) :=
  stoppedBornPrefixLaw P.seedLaw ρ (activePrefix P.toRawRules) (activePrefix_measurable P.toRawRules)
    (prefixSetting P.toRawRules) (prefixSetting_measurable P.toRawRules) m

instance executionPrefixLaw_probability (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) : IsProbabilityMeasure (executionPrefixLaw P ρ m) := by
  unfold executionPrefixLaw
  infer_instance

/-- No postulated consistency restriction: the actual Born executor has mass one on legal histories. -/
theorem executionPrefixLaw_ae_consistent (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    ∀ᵐ h ∂executionPrefixLaw P ρ m, ConsistentPrefix P.toRawRules m h := by
  exact prefixLaw_ae_consistent P.toRawRules P.seedLaw
    (fun t => controlledProductBornKernel d n ρ (prefixSetting P.toRawRules t)
      (prefixSetting_measurable P.toRawRules t)) m

/-- Actual full-record decoding is measurable on the uncompleted prefix sigma algebra. -/
theorem execution_full_record_measurable (P : QuditProtocol Z d n) (m : ℕ) :
    Measurable (execPrefix P.toRawRules m) := execPrefix_measurable P.toRawRules m

/-- Information for the two actual source-dependent executions of the same raw protocol.
The integral counts physical requests; the infinite-trajectory T∧m identification is a separate theorem. -/
theorem executionPrefixLaw_klDiv_le (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) (m : ℕ) :
    klDiv (executionPrefixLaw P ρ m) (executionPrefixLaw P σ m) ≤
      L * ∫⁻ h, prefixActiveCount (activePrefix P.toRawRules) m h ∂executionPrefixLaw P ρ m :=
  stoppedBornPrefixLaw_klDiv_le P.seedLaw ρ σ (activePrefix P.toRawRules)
    (activePrefix_measurable P.toRawRules) (prefixSetting P.toRawRules)
    (prefixSetting_measurable P.toRawRules) L hL m

end LocalCertification.Protocol
