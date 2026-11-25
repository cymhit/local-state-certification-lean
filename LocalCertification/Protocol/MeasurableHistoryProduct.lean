import LocalCertification.Protocol.MeasurableHistoryEncoding
import LocalCertification.Protocol.MeasurableExecutionProduct

/-! An independently specified time/history-indexed local-product experiment,
and its compiler into the setting-family executor. The direct kernel is formed
from the original history and actual local POVMs before any augmented settings
are introduced. Arbitrary measurable seed, label, and local outcome spaces are
retained; there are no countability or standard-Borel assumptions. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Quantum
open LocalCertification.Information.KernelHistory
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

/-- Totalized local history kernels. A live-only representation can extend
inactive histories arbitrarily, since the direct kernel uses empty padding there. -/
structure HistoryProductProtocol (d n : ℕ) (Z L : Type u) (Ω : Fin n → Type u)
    [MeasurableSpace Z] [MeasurableSpace L] [∀ i, MeasurableSpace (Ω i)]
    extends RawProtocol Z L ((i : Fin n) → Ω i) where
  localMeasurements : (t : ℕ) → ∀ i : Fin n,
    POVMKernel (Z × (Fin t → L × ((i : Fin n) → Ω i))) (Ω i) (Fin d)

namespace HistoryProductProtocol
variable {d n : ℕ} [NeZero d] {Z L : Type u} {Ω : Fin n → Type u}
  [MeasurableSpace Z] [MeasurableSpace L] [∀ i, MeasurableSpace (Ω i)]
variable (P : HistoryProductProtocol d n Z L Ω)

def globalMeasurements (t : ℕ) := POVMKernel.product (P.localMeasurements t)

/-- The direct conditional law at the original classical state. -/
def directStateKernel (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    Kernel (Z × State L ((i : Fin n) → Ω i) t) (Slot ((i : Fin n) → Ω i)) where
  toFun p := match p.2 with
    | Sum.inl _ => Measure.dirac (Sum.inl ())
    | Sum.inr v => (((P.globalMeasurements t).bornKernel ρ).map Sum.inr) (p.1, v.1)
  measurable' := by
    have hl := (((P.globalMeasurements t).bornKernel ρ).map
      (Sum.inr : ((i : Fin n) → Ω i) → Slot ((i : Fin n) → Ω i))).measurable.comp
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
    have := Kernel.IsMarkovKernel.map ((P.globalMeasurements t).bornKernel ρ)
      (measurable_inr : Measurable (Sum.inr : ((i : Fin n) → Ω i) → Slot ((i : Fin n) → Ω i)))
    rcases p with ⟨z, j | v⟩
    · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (Sum.inl () : Slot ((i : Fin n) → Ω i))))
    · exact inferInstanceAs (IsProbabilityMeasure
        ((((P.globalMeasurements t).bornKernel ρ).map Sum.inr) (z, v.1)))

def kernel (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    Kernel (History Z ((i : Fin n) → Ω i) t) (Slot ((i : Fin n) → Ω i)) :=
  (P.directStateKernel ρ t).comap
    (fun h => (historySeed t h, state P.toRawRules t h))
    ((historySeed_measurable t).prodMk (state_measurable P.toRawRules t))

instance kernel_markov (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    IsMarkovKernel (P.kernel ρ t) := by unfold kernel; infer_instance

theorem kernel_apply (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ)
    (h : History Z ((i : Fin n) → Ω i) t) :
    P.kernel ρ t h = match state P.toRawRules t h with
      | Sum.inl _ => Measure.dirac (Sum.inl ())
      | Sum.inr v => ((MeasurablePOVM.product
          (fun i => (P.localMeasurements t i).measurement (historySeed t h, v.1))).born ρ).map Sum.inr := by
  simp only [kernel, Kernel.comap_apply, directStateKernel]
  cases state P.toRawRules t h with
  | inl j => rfl
  | inr v => exact Kernel.map_apply _ measurable_inr _

/-- The original history-dependent experiment is defined by iteration of its
direct kernels, without reference to the compiler or to an assumed law. -/
def law (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    Measure (Sample Z (Slot ((i : Fin n) → Ω i))) := executionLaw P.seedLaw (P.kernel ρ)

instance law_probability (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    IsProbabilityMeasure (P.law ρ) := by unfold law; infer_instance

def time := stoppingTime P.toRawRules
def reportedDecision := terminalDecision P.toRawRules
def expectedCopies (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : ℝ≥0∞ :=
  ∫⁻ p, cost P.toRawRules p ∂P.law ρ
def Terminates (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : Prop :=
  ∀ᵐ p ∂P.law ρ, P.time p ≠ ⊤
def Capped (N : ℕ) : Prop := MeasurableExecution.Capped P.toRawRules N
def Valid (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : Prop :=
  (∀ ρ, a ≤ pureTargetFidelity ψ ρ →
    P.Terminates ρ ∧ P.law ρ {p | P.reportedDecision p = 1} ≤ ENNReal.ofReal δ) ∧
  (∀ ρ, pureTargetFidelity ψ ρ ≤ b →
    P.Terminates ρ ∧ P.law ρ {p | P.reportedDecision p = 0} ≤ ENNReal.ofReal δ)

def settingFamily (i : Fin n) :
    POVMKernel (HistorySetting Z L ((i : Fin n) → Ω i)) (Ω i) (Fin d) where
  measurement s := (P.localMeasurements s.2.1 i).measurement s.2.2
  measurable_effect A hA := by
    have hm : Measurable (fun c : HistoryContext Z L ((i : Fin n) → Ω i) =>
        ((P.localMeasurements c.1 i).measurement c.2).toVectorMeasure A) := by
      apply HistoryEncoding.measurable_from_sigma
      intro t
      exact (P.localMeasurements t i).measurable_effect A hA
    exact hm.comp measurable_snd

def compile : ProductProtocol d n Z (HistorySetting Z L ((i : Fin n) → Ω i)) Ω where
  toRawRules := HistoryEncoding.rules P.toRawRules
  seedLaw := P.seedLaw
  seed_probability := P.seed_probability
  localFamilies := P.settingFamily

omit [NeZero d] in
theorem compile_seedLaw : P.compile.seedLaw = P.seedLaw := rfl

theorem compile_measurement (t : ℕ) (h : Z × (Fin t → L × ((i : Fin n) → Ω i))) (l : L) :
    P.compile.toBorn.measurements.measurement (l, ⟨t, h⟩) =
      MeasurablePOVM.product (fun i => (P.localMeasurements t i).measurement h) := rfl

theorem compile_kernel (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    P.compile.toBorn.kernel ρ t = P.kernel ρ t := by
  ext1 h
  rw [BornProtocol.kernel_apply, P.kernel_apply]
  rw [show P.compile.toBorn.toRawRules = HistoryEncoding.rules P.toRawRules from rfl]
  rw [← HistoryEncoding.state_projection P.toRawRules t h]
  cases hs : state (HistoryEncoding.rules P.toRawRules) t h with
  | inl j => rfl
  | inr v =>
    have hc := HistoryEncoding.state_context P.toRawRules t h v hs
    change ((MeasurablePOVM.product (fun i =>
      (P.localMeasurements v.2.2.1 i).measurement v.2.2.2)).born ρ).map Sum.inr =
      ((MeasurablePOVM.product (fun i =>
      (P.localMeasurements t i).measurement (historySeed t h, HistoryEncoding.eraseRecords v.1))).born ρ).map Sum.inr
    rw [hc]

theorem compile_law (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    P.compile.toBorn.law ρ = P.law ρ := by
  change executionLaw P.seedLaw (P.compile.toBorn.kernel ρ) = executionLaw P.seedLaw (P.kernel ρ)
  congr 1
  funext t
  exact P.compile_kernel ρ t

theorem compile_time (p : Sample Z (Slot ((i : Fin n) → Ω i))) :
    P.compile.toBorn.time p = P.time p := HistoryEncoding.time_eq P.toRawRules p

theorem compile_decision (p : Sample Z (Slot ((i : Fin n) → Ω i))) :
    P.compile.toBorn.reportedDecision p = P.reportedDecision p := HistoryEncoding.decision_eq P.toRawRules p

omit [NeZero d] in
theorem compile_legal (p : Sample Z (Slot ((i : Fin n) → Ω i))) :
    Legal P.compile.toRawRules p ↔ Legal P.toRawRules p := HistoryEncoding.legal_iff P.toRawRules p

theorem compile_expectedCopies (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    P.compile.toBorn.expectedCopies ρ = P.expectedCopies ρ := by
  unfold BornProtocol.expectedCopies expectedCopies
  rw [P.compile_law]
  apply lintegral_congr
  intro p
  exact congrArg ENat.toENNReal (P.compile_time p)

theorem compile_terminates_iff (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    P.compile.toBorn.Terminates ρ ↔ P.Terminates ρ := by
  unfold BornProtocol.Terminates Terminates
  rw [P.compile_law]
  simp only [P.compile_time]

theorem compile_valid_iff (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    P.compile.toBorn.Valid ψ a b δ ↔ P.Valid ψ a b δ := by
  unfold BornProtocol.Valid Valid
  simp only [P.compile_terminates_iff, P.compile_law, P.compile_decision]

theorem compile_capped_iff (N : ℕ) : P.compile.toBorn.Capped N ↔ P.Capped N :=
  HistoryEncoding.capped_iff P.toRawRules N

theorem law_prefix (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℕ) :
    (P.law ρ).map (rawPrefix t) = prefixLaw P.seedLaw (P.kernel ρ) t :=
  executionLaw_prefix P.seedLaw (P.kernel ρ) t

end HistoryProductProtocol
end LocalCertification.Protocol.MeasurableExecution
