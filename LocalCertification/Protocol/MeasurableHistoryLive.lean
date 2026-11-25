import LocalCertification.Protocol.MeasurableExecutionProduct
import LocalCertification.Quantum.MeasurablePOVMProductFactors

/-! History-dependent product measurements specified only on continuing
histories. Measurability is required of the global product POVM, as in the
paper. No measurement is required on a stopped history. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Quantum
open LocalCertification.Information.KernelHistory
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace LocalCertification.Protocol.MeasurableExecution
universe u

def continuingContexts {Z L O : Type u}
    [MeasurableSpace Z] [MeasurableSpace L] [MeasurableSpace O]
    (R : RawRules Z L O) (t : ℕ) : Set (Z × (Fin t → L × O)) :=
  {h | ∃ s, R.rule t h = Sum.inr s}

theorem continuingContexts_measurable {Z L O : Type u}
    [MeasurableSpace Z] [MeasurableSpace L] [MeasurableSpace O]
    (R : RawRules Z L O) (t : ℕ) : MeasurableSet (continuingContexts R t) := by
  have hm := (R.measurable_rule t) measurableSet_range_inr
  simpa only [continuingContexts, Set.preimage, Set.mem_range, eq_comm] using hm

/-- A live reconstructed state carries the setting selected by the original
rule at that exact seed and complete history, on every prefix. -/
theorem state_rule_of_live {Z L O : Type u}
    [MeasurableSpace Z] [MeasurableSpace L] [MeasurableSpace O]
    (R : RawRules Z L O) (t : ℕ) (h : History Z O t)
    (v : (Fin t → L × O) × L) (hv : state R t h = Sum.inr v) :
    R.rule t (historySeed t h, v.1) = Sum.inr v.2 := by
  cases t with
  | zero =>
    change withAction Fin.elim0 (R.rule 0 (h, Fin.elim0)) = Sum.inr v at hv
    cases ha : R.rule 0 (h, Fin.elim0) with
    | inl j => simp [ha, withAction] at hv
    | inr s => simp [ha, withAction] at hv; subst v; exact ha
  | succ t =>
    change advance R (historySeed t h.1) (state R t h.1) h.2 = Sum.inr v at hv
    cases hs : state R t h.1 with
    | inl j => simp [hs, advance] at hv
    | inr w =>
      cases ho : h.2 with
      | inl e => simp [hs, ho, advance] at hv
      | inr x =>
        simp only [hs, ho, advance] at hv
        cases ha : R.rule (t+1) (historySeed t h.1, Fin.snoc w.1 (w.2, x)) with
        | inl j => simp [ha, withAction] at hv
        | inr s => simp [ha, withAction] at hv; subst v; exact ha

/-- The literal live-history input: an actual global product POVM with
eventwise measurable effects. Local factors are not assumed measurable. -/
structure PaperHistoryProduct (d n : ℕ) [NeZero d] (Z L : Type u) (Ω : Fin n → Type u)
    [MeasurableSpace Z] [MeasurableSpace L] [∀ i, MeasurableSpace (Ω i)] where
  raw : RawProtocol Z L ((i : Fin n) → Ω i)
  measurements : (t : ℕ) → POVMKernel
    {h // h ∈ continuingContexts raw.toRawRules t}
    ((i : Fin n) → Ω i) (CertificationGaussian.QuditIndex d n)
  product_measurement : ∀ t h, ∃ M : ∀ i, MeasurablePOVM (Ω i) (Fin d),
    (measurements t).measurement h = MeasurablePOVM.product M

namespace PaperHistoryProduct
variable {d n : ℕ} [NeZero d] {Z L : Type u} {Ω : Fin n → Type u}
  [MeasurableSpace Z] [MeasurableSpace L] [∀ i, MeasurableSpace (Ω i)]
variable (P : PaperHistoryProduct d n Z L Ω)

/-- Extract measurable local factors from the global product kernel. -/
def localMeasurements (t : ℕ) : ∀ i, POVMKernel
    {h // h ∈ continuingContexts P.raw.toRawRules t} (Ω i) (Fin d) :=
  Classical.choose (POVMKernel.exists_product_factors (P.measurements t) (P.product_measurement t))

theorem product_localMeasurements (t : ℕ) :
    POVMKernel.product (P.localMeasurements t) = P.measurements t :=
  Classical.choose_spec (POVMKernel.exists_product_factors (P.measurements t) (P.product_measurement t))

/-- A whole-record kernel, with common empty padding on noncontinuing contexts.
Its definition has no compiler or setting-family executor as an input. -/
def contextKernel (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    Kernel (Z × (Fin t → L × ((i : Fin n) → Ω i))) (Slot ((i : Fin n) → Ω i)) where
  toFun h := if hc : h ∈ continuingContexts P.raw.toRawRules t then
      (((P.measurements t).bornKernel ρ).map Sum.inr) ⟨h, hc⟩
    else Measure.dirac (Sum.inl ())
  measurable' := by
    exact (((P.measurements t).bornKernel ρ).map Sum.inr).measurable.dite
      measurable_const (continuingContexts_measurable P.raw.toRawRules t)

instance contextKernel_markov (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    IsMarkovKernel (P.contextKernel ρ t) where
  isProbabilityMeasure h := by
    have := Kernel.IsMarkovKernel.map ((P.measurements t).bornKernel ρ)
      (measurable_inr : Measurable (Sum.inr : ((i : Fin n) → Ω i) → Slot ((i : Fin n) → Ω i)))
    change IsProbabilityMeasure (if hc : h ∈ continuingContexts P.raw.toRawRules t then
      (((P.measurements t).bornKernel ρ).map Sum.inr) ⟨h, hc⟩ else Measure.dirac (Sum.inl ()))
    split <;> infer_instance

def directStateKernel (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    Kernel (Z × State L ((i : Fin n) → Ω i) t) (Slot ((i : Fin n) → Ω i)) where
  toFun p := match p.2 with
    | Sum.inl _ => Measure.dirac (Sum.inl ())
    | Sum.inr v => P.contextKernel ρ t (p.1, v.1)
  measurable' := by
    have hl := (P.contextKernel ρ t).measurable.comp
      ((measurable_fst : Measurable (Prod.fst : Z × ((Fin t → L × ((i : Fin n) → Ω i)) × L) → Z)).prodMk
        (measurable_fst.comp measurable_snd))
    have hs : Measurable (fun _ : Z × Fin 2 =>
        Measure.dirac (Sum.inl () : Slot ((i : Fin n) → Ω i))) := measurable_const
    convert (hs.sumElim hl).comp
      (MeasurableEquiv.prodSumDistrib Z (Fin 2) ((Fin t → L × ((i : Fin n) → Ω i)) × L)).measurable using 1
    funext p
    rcases p with ⟨z, j | v⟩ <;> rfl

instance directStateKernel_markov (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    IsMarkovKernel (P.directStateKernel ρ t) where
  isProbabilityMeasure p := by
    rcases p with ⟨z, j | v⟩
    · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (Sum.inl () : Slot ((i : Fin n) → Ω i))))
    · exact inferInstanceAs (IsProbabilityMeasure (P.contextKernel ρ t (z, v.1)))

def kernel (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    Kernel (History Z ((i : Fin n) → Ω i) t) (Slot ((i : Fin n) → Ω i)) :=
  (P.directStateKernel ρ t).comap
    (fun h => (historySeed t h, state P.raw.toRawRules t h))
    ((historySeed_measurable t).prodMk (state_measurable P.raw.toRawRules t))

instance kernel_markov (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    IsMarkovKernel (P.kernel ρ t) := by unfold kernel; infer_instance

theorem kernel_apply (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ)
    (h : History Z ((i : Fin n) → Ω i) t) :
    P.kernel ρ t h = match state P.raw.toRawRules t h with
      | Sum.inl _ => Measure.dirac (Sum.inl ())
      | Sum.inr v => P.contextKernel ρ t (historySeed t h, v.1) := rfl

def law (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    Measure (Sample Z (Slot ((i : Fin n) → Ω i))) := executionLaw P.raw.seedLaw (P.kernel ρ)

instance law_probability (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    IsProbabilityMeasure (P.law ρ) := by unfold law; infer_instance

def time := stoppingTime P.raw.toRawRules
def reportedDecision := terminalDecision P.raw.toRawRules
def expectedCopies (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : ℝ≥0∞ :=
  ∫⁻ p, cost P.raw.toRawRules p ∂P.law ρ
def Terminates (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : Prop :=
  ∀ᵐ p ∂P.law ρ, P.time p ≠ ⊤
def Capped (N : ℕ) : Prop := MeasurableExecution.Capped P.raw.toRawRules N
def Valid (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : Prop :=
  (∀ ρ, a ≤ pureTargetFidelity ψ ρ →
    P.Terminates ρ ∧ P.law ρ {p | P.reportedDecision p = 1} ≤ ENNReal.ofReal δ) ∧
  (∀ ρ, pureTargetFidelity ψ ρ ≤ b →
    P.Terminates ρ ∧ P.law ρ {p | P.reportedDecision p = 0} ≤ ENNReal.ofReal δ)

/-- Exact observable preservation by a compiled setting-family protocol.
These are conclusions to prove, not fields of the paper's input model. -/
structure Preserves {S : Type u} [MeasurableSpace S]
    (Q : ProductProtocol d n Z S Ω) : Prop where
  law_eq : ∀ ρ, Q.toBorn.law ρ = P.law ρ
  time_eq : ∀ p, Q.toBorn.time p = P.time p
  decision_eq : ∀ p, Q.toBorn.reportedDecision p = P.reportedDecision p
  legal_iff : ∀ p, Legal Q.toRawRules p ↔ Legal P.raw.toRawRules p

namespace Preserves
variable {P} {S : Type u} [MeasurableSpace S] {Q : ProductProtocol d n Z S Ω}
variable (h : P.Preserves Q)
include h

theorem expectedCopies_eq (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    Q.toBorn.expectedCopies ρ = P.expectedCopies ρ := by
  unfold BornProtocol.expectedCopies PaperHistoryProduct.expectedCopies
  rw [h.law_eq]
  apply lintegral_congr
  intro p
  exact congrArg ENat.toENNReal (h.time_eq p)

theorem terminates_iff (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    Q.toBorn.Terminates ρ ↔ P.Terminates ρ := by
  unfold BornProtocol.Terminates PaperHistoryProduct.Terminates
  rw [h.law_eq]
  simp only [h.time_eq]

theorem valid_iff (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    Q.toBorn.Valid ψ a b δ ↔ P.Valid ψ a b δ := by
  unfold BornProtocol.Valid PaperHistoryProduct.Valid
  simp only [h.terminates_iff, h.law_eq, h.decision_eq]

theorem capped_iff (N : ℕ) : Q.toBorn.Capped N ↔ P.Capped N := by
  change (∀ p, Legal Q.toRawRules p → Q.toBorn.time p ≤ (N : ℕ∞)) ↔
    (∀ p, Legal P.raw.toRawRules p → P.time p ≤ (N : ℕ∞))
  simp only [h.legal_iff, h.time_eq]

end Preserves

end PaperHistoryProduct
end LocalCertification.Protocol.MeasurableExecution
