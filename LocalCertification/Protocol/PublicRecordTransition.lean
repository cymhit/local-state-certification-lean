import LocalCertification.Protocol.ConditionalBorn

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- The actual next full execution state is obtained by appending the already chosen setting and Born outcome. -/
theorem executionSlotKernel_public_active (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ)
    (h : SlotHistory Z (CertificationGaussian.QuditIndex d n) m) (ha : h ∈ activePrefix P.toRawRules m) :
    (executionSlotKernel P ρ m h).map
      (fun o => advance P.toRawRules (slotSeed m h) (execPrefix P.toRawRules m h) o) =
      (productBornMeasure d n (prefixSetting P.toRawRules m h) ρ).map
        (fun x => appendOutcome P.toRawRules (slotSeed m h) (execPrefix P.toRawRules m h) x) := by
  rw [executionSlotKernel, stopContinue_apply, ite_eq_left ha,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable Option.some)]
  apply congrArg (Measure.map · (productBornMeasure d n (prefixSetting P.toRawRules m h) ρ))
  funext x
  change (if actionContinues (execPrefix P.toRawRules m h).2 = true then _ else _) = _
  exact ite_eq_left (show actionContinues (execPrefix P.toRawRules m h).2 = true from ha)

/-- Stopping produces actual empty padding and preserves the stopped decision, independently of input state. -/
theorem executionSlotKernel_public_stopped (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ)
    (h : SlotHistory Z (CertificationGaussian.QuditIndex d n) m) (ha : h ∉ activePrefix P.toRawRules m) :
    (executionSlotKernel P ρ m h).map
      (fun o => advance P.toRawRules (slotSeed m h) (execPrefix P.toRawRules m h) o) =
      Measure.dirac (appendEmpty (execPrefix P.toRawRules m h) (execPrefix P.toRawRules m h).2) := by
  rw [executionSlotKernel, stopContinue_apply, ite_eq_right ha,
    Measure.map_dirac' (measurable_of_countable _) none]
  congr 1
  exact ite_eq_right ha

/-- The new public record itself contains the deterministic full setting paired with the physical Born draw. -/
theorem executionSlotKernel_record_active (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ)
    (h : SlotHistory Z (CertificationGaussian.QuditIndex d n) m) (ha : h ∈ activePrefix P.toRawRules m) :
    (executionSlotKernel P ρ m h).map
      (fun o => (advance P.toRawRules (slotSeed m h) (execPrefix P.toRawRules m h) o).1 (Fin.last m)) =
      (productBornMeasure d n (prefixSetting P.toRawRules m h) ρ).map
        (fun x => Sum.inr (prefixSetting P.toRawRules m h, x) : CertificationGaussian.QuditIndex d n → PaddedRecord (ProductSetting d n) (CertificationGaussian.QuditIndex d n)) := by
  rw [executionSlotKernel, stopContinue_apply, ite_eq_left ha,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable Option.some)]
  apply congrArg (Measure.map · (productBornMeasure d n (prefixSetting P.toRawRules m h) ρ))
  funext x
  have ha' : actionContinues (execPrefix P.toRawRules m h).2 = true := ha
  simp only [Function.comp_apply, advance, ite_eq_left ha', appendOutcome, Fin.snoc_last]
  rfl

/-- The complete next-prefix law is exactly the actual finite-kernel recursion pushed through the full public update. -/
theorem executionPrefixLaw_public_succ (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    (executionPrefixLaw P ρ (m+1)).map (publicPrefix P.toRawRules (m+1)) =
      (executionPrefixLaw P ρ m ⊗ₘ executionSlotKernel P ρ m).map
        (fun p => (slotSeed m p.1, advance P.toRawRules (slotSeed m p.1) (execPrefix P.toRawRules m p.1) p.2)) := rfl

end LocalCertification.Protocol
