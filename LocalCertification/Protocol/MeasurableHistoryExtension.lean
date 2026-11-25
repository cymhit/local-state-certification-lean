import LocalCertification.Protocol.MeasurableHistoryLive
import LocalCertification.Protocol.MeasurableHistoryProduct

/-! Extending measurements off the continuing histories does not change any
executed kernel. A default is extracted from an actual continuing measurement
when one exists, so no nonempty-outcome premise is introduced. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Quantum
open LocalCertification.Information.KernelHistory
noncomputable section
attribute [local instance] Classical.propDecidable
namespace LocalCertification.Protocol.MeasurableExecution
universe u
namespace PaperHistoryProduct
variable {d n : ℕ} [NeZero d] {Z L : Type u} {Ω : Fin n → Type u}
  [MeasurableSpace Z] [MeasurableSpace L] [∀ i, MeasurableSpace (Ω i)]
variable (P : PaperHistoryProduct d n Z L Ω)

def extendedLocal (M₀ : ∀ i, MeasurablePOVM (Ω i) (Fin d)) (t : ℕ) (i : Fin n) :
    POVMKernel (Z × (Fin t → L × ((i : Fin n) → Ω i))) (Ω i) (Fin d) where
  measurement h := if hc : h ∈ continuingContexts P.raw.toRawRules t then
    (P.localMeasurements t i).measurement ⟨h, hc⟩ else M₀ i
  measurable_effect A hA := by
    convert ((P.localMeasurements t i).measurable_effect A hA).dite
      (g := fun _ => (M₀ i).toVectorMeasure A)
      measurable_const (continuingContexts_measurable P.raw.toRawRules t) using 1
    funext h
    split <;> rfl

def total (M₀ : ∀ i, MeasurablePOVM (Ω i) (Fin d)) : HistoryProductProtocol d n Z L Ω where
  toRawProtocol := P.raw
  localMeasurements := P.extendedLocal M₀

theorem total_kernel (M₀ : ∀ i, MeasurablePOVM (Ω i) (Fin d))
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    (P.total M₀).kernel ρ t = P.kernel ρ t := by
  ext1 h
  rw [HistoryProductProtocol.kernel_apply, P.kernel_apply]
  change (match state P.raw.toRawRules t h with
    | Sum.inl _ => _
    | Sum.inr v => _) = _
  cases hs : state P.raw.toRawRules t h with
  | inl j => rfl
  | inr v =>
    have hc : (historySeed t h, v.1) ∈ continuingContexts P.raw.toRawRules t :=
      ⟨v.2, state_rule_of_live P.raw.toRawRules t h v hs⟩
    have he : MeasurablePOVM.product (fun i =>
        ((P.total M₀).localMeasurements t i).measurement (historySeed t h, v.1)) =
        (P.measurements t).measurement ⟨(historySeed t h, v.1), hc⟩ := by
      change MeasurablePOVM.product (fun i =>
        if hc' : (historySeed t h, v.1) ∈ continuingContexts P.raw.toRawRules t then
          (P.localMeasurements t i).measurement ⟨(historySeed t h, v.1), hc'⟩ else M₀ i) = _
      simp only [dite_eq_left hc]
      exact congrArg (fun K => K.measurement ⟨(historySeed t h, v.1), hc⟩)
        (P.product_localMeasurements t)
    change (MeasurablePOVM.born _ ρ).map Sum.inr = _
    rw [he]
    change _ = if hc' : (historySeed t h, v.1) ∈ continuingContexts P.raw.toRawRules t then
      (((P.measurements t).bornKernel ρ).map Sum.inr) ⟨(historySeed t h, v.1), hc'⟩
      else Measure.dirac (Sum.inl ())
    rw [dite_eq_left hc]
    exact (Kernel.map_apply ((P.measurements t).bornKernel ρ)
      (measurable_inr : Measurable (Sum.inr : ((i : Fin n) → Ω i) → Slot ((i : Fin n) → Ω i))) _).symm

theorem total_law (M₀ : ∀ i, MeasurablePOVM (Ω i) (Fin d))
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (P.total M₀).law ρ = P.law ρ := by
  change executionLaw P.raw.seedLaw ((P.total M₀).kernel ρ) = executionLaw P.raw.seedLaw (P.kernel ρ)
  congr 1
  funext t
  exact P.total_kernel M₀ ρ t

theorem total_compile_preserves (M₀ : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    P.Preserves (P.total M₀).compile where
  law_eq ρ := ((P.total M₀).compile_law ρ).trans (P.total_law M₀ ρ)
  time_eq p := (P.total M₀).compile_time p
  decision_eq p := (P.total M₀).compile_decision p
  legal_iff p := (P.total M₀).compile_legal p

theorem exists_compile_of_live
    (h : ∃ t, Nonempty {h // h ∈ continuingContexts P.raw.toRawRules t}) :
    ∃ Q : ProductProtocol d n Z (HistorySetting Z L ((i : Fin n) → Ω i)) Ω, P.Preserves Q := by
  obtain ⟨t, ⟨h⟩⟩ := h
  let M₀ := fun i => (P.localMeasurements t i).measurement h
  exact ⟨(P.total M₀).compile, P.total_compile_preserves M₀⟩

end PaperHistoryProduct
end LocalCertification.Protocol.MeasurableExecution
