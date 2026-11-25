import LocalCertification.Protocol.MeasurableHistoryLive

/-! Every setting-indexed product protocol is a literal live-history product
experiment. The selected setting is recovered only on the continuing subtype,
so no default setting or nonempty outcome hypothesis is required. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Quantum
open LocalCertification.Information.KernelHistory
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

/-- The original setting chosen by a continuing rule, without totalization. -/
def selectedHistorySetting {Z S O : Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    (R : RawRules Z S O) (t : ℕ)
    (h : {h // h ∈ continuingContexts R t}) : S :=
  Classical.choose h.property

theorem selectedHistorySetting_spec {Z S O : Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    (R : RawRules Z S O) (t : ℕ) (h : {h // h ∈ continuingContexts R t}) :
    R.rule t h.val = Sum.inr (selectedHistorySetting R t h) :=
  Classical.choose_spec h.property

/-- The continuation inclusion has the original coproduct sigma algebra.
Measurability follows from preimages of measurable images under `Sum.inr`. -/
theorem selectedHistorySetting_measurable {Z S O : Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    (R : RawRules Z S O) (t : ℕ) : Measurable (selectedHistorySetting R t) := by
  intro A hA
  have hm := ((R.measurable_rule t).comp
    (measurable_subtype_coe : Measurable
      (Subtype.val : {h // h ∈ continuingContexts R t} → Z × (Fin t → S × O))))
    (hA.inr_image : MeasurableSet (Sum.inr '' A : Set (Action S)))
  convert hm using 1
  ext h
  simp [selectedHistorySetting_spec]

namespace PaperHistoryProduct
variable {d n : ℕ} [NeZero d] {Z S : Type u} {Ω : Fin n → Type u}
  [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]

/-- Retain the raw protocol literally and select its actual product POVM
using the setting carried by its continuing action. -/
def ofSetting (Q : ProductProtocol d n Z S Ω) : PaperHistoryProduct d n Z S Ω where
  raw := Q.toRawProtocol
  measurements t := (POVMKernel.product Q.localFamilies).reindex
    (selectedHistorySetting Q.toRawRules t) (selectedHistorySetting_measurable Q.toRawRules t)
  product_measurement t h :=
    ⟨fun i => (Q.localFamilies i).measurement (selectedHistorySetting Q.toRawRules t h), rfl⟩

theorem ofSetting_kernel (Q : ProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    (ofSetting Q).kernel ρ t = Q.toBorn.kernel ρ t := by
  classical
  ext1 h
  rw [PaperHistoryProduct.kernel_apply, BornProtocol.kernel_apply]
  rw [show Q.toBorn.toRawRules = Q.toRawRules from rfl]
  change (match state Q.toRawRules t h with
    | Sum.inl _ => _
    | Sum.inr v => _) = _
  cases hs : state Q.toRawRules t h with
  | inl j => rfl
  | inr v =>
    have hc : (historySeed t h, v.1) ∈ continuingContexts Q.toRawRules t :=
      ⟨v.2, state_rule_of_live Q.toRawRules t h v hs⟩
    have hsel : selectedHistorySetting Q.toRawRules t ⟨(historySeed t h, v.1), hc⟩ = v.2 :=
      Sum.inr_injective ((selectedHistorySetting_spec Q.toRawRules t _).symm.trans
        (state_rule_of_live Q.toRawRules t h v hs))
    change (if hc' : (historySeed t h, v.1) ∈ continuingContexts Q.toRawRules t then
      ((((ofSetting Q).measurements t).bornKernel ρ).map Sum.inr)
        ⟨(historySeed t h, v.1), hc'⟩ else Measure.dirac (Sum.inl ())) = _
    rw [dite_eq_left hc, Kernel.map_apply _ measurable_inr _]
    change ((MeasurablePOVM.product (fun i => (Q.localFamilies i).measurement
      (selectedHistorySetting Q.toRawRules t ⟨(historySeed t h, v.1), hc⟩))).born ρ).map Sum.inr = _
    rw [hsel]
    rfl

theorem ofSetting_law (Q : ProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (ofSetting Q).law ρ = Q.toBorn.law ρ := by
  change executionLaw Q.seedLaw ((ofSetting Q).kernel ρ) =
    executionLaw Q.seedLaw (Q.toBorn.kernel ρ)
  congr 1
  funext t
  exact ofSetting_kernel Q ρ t

/-- The converse embedding preserves the independently iterated law and all
literal stopping/decision/legal-path observables. -/
theorem ofSetting_preserves (Q : ProductProtocol d n Z S Ω) :
    (ofSetting Q).Preserves Q where
  law_eq ρ := (ofSetting_law Q ρ).symm
  time_eq _ := rfl
  decision_eq _ := rfl
  legal_iff _ := Iff.rfl

end PaperHistoryProduct
end LocalCertification.Protocol.MeasurableExecution
