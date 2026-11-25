import LocalCertification.Protocol.MeasurableExecutionTransport
import LocalCertification.Protocol.MeasurableExecutionProduct
import LocalCertification.Quantum.MeasurablePOVMProductMap

/-! Literal original spaces may occupy three independent universes. Alignment
uses a bijective measurable lift; no label, null branch or seed is discarded. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory LocalCertification.Quantum
open LocalCertification.Information.KernelHistory
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u v w

/-- The original arbitrary-universe local-product protocol carries only its
common seed, causal rules and actual original local measurement families. -/
structure OriginalProductProtocol (d n : ℕ) (Z : Type u) (S : Type v) (Ω : Fin n → Type w)
    [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
    extends RawProtocol Z S ((i : Fin n) → Ω i) where
  localFamilies : ∀ i, POVMKernel S (Ω i) (Fin d)

namespace OriginalProductProtocol
variable {d n : ℕ} [NeZero d] {Z : Type u} {S : Type v} {Ω : Fin n → Type w}
  [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]

abbrev LiteralSample (Z : Type u) (Ω : Fin n → Type w) := Z × (ℕ → Unit ⊕ ((i : Fin n) → Ω i))

def sampleEquiv : LiteralSample Z Ω ≃ᵐ
    Sample (ULift.{max u v w} Z) (Slot ((i : Fin n) → ULift.{max u v w} (Ω i))) :=
  MeasurableEquiv.prodCongr MeasurableEquiv.ulift.symm
    (MeasurableEquiv.piCongrRight (fun _ =>
      MeasurableEquiv.sumCongr (MeasurableEquiv.refl Unit)
        (MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.ulift.symm))))

def fullSampleEquiv : (Z × (ℕ → Unit ⊕ (S × ((i : Fin n) → Ω i)))) ≃ᵐ
    Sample (ULift.{max u v w} Z)
      (Unit ⊕ (ULift.{max u v w} S × ((i : Fin n) → ULift.{max u v w} (Ω i)))) :=
  MeasurableEquiv.prodCongr MeasurableEquiv.ulift.symm
    (MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.sumCongr (MeasurableEquiv.refl Unit)
      (MeasurableEquiv.prodCongr MeasurableEquiv.ulift.symm
        (MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.ulift.symm)))))

def aligned (P : OriginalProductProtocol d n Z S Ω) :
    ProductProtocol d n (ULift.{max u v w} Z) (ULift.{max u v w} S)
      (fun i => ULift.{max u v w} (Ω i)) where
  rule m p := Sum.map id ULift.up
    (P.rule m (p.1.down, fun i => ((p.2 i).1.down, fun k => ((p.2 i).2 k).down)))
  measurable_rule m := by
    apply (measurable_id.sumMap measurable_up).comp
    apply (P.measurable_rule m).comp
    apply (measurable_down.comp measurable_fst).prodMk
    apply measurable_pi_iff.mpr
    intro i
    apply (measurable_down.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))).prodMk
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_down.comp ((measurable_pi_apply k).comp
      (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)))
  seedLaw := P.seedLaw.map ULift.up
  seed_probability := by
    constructor
    rw [Measure.map_apply measurable_up MeasurableSet.univ]
    exact measure_univ
  localFamilies i := ((P.localFamilies i).map ULift.up measurable_up).reindex ULift.down measurable_down

theorem aligned_kernel (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (s : S) :
    P.aligned.toBorn.measurements.bornKernel ρ (ULift.up s) =
      ((MeasurablePOVM.product (fun i => (P.localFamilies i).measurement s)).born ρ).map
        (fun x i => ULift.up (x i)) :=
  MeasurablePOVM.product_born_map (fun i => (P.localFamilies i).measurement s)
    (fun _ => ULift.up) (fun _ => measurable_up) ρ

def law (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : Measure (LiteralSample Z Ω) :=
  (P.aligned.toBorn.law ρ).map sampleEquiv.{u,v,w}.symm

instance law_probability (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : IsProbabilityMeasure (P.law ρ) := by
  constructor
  rw [law, Measure.map_apply sampleEquiv.symm.measurable MeasurableSet.univ]
  exact measure_univ

def time (P : OriginalProductProtocol d n Z S Ω) : LiteralSample Z Ω → ℕ∞ :=
  P.aligned.toBorn.time ∘ sampleEquiv.{u,v,w}
def reportedDecision (P : OriginalProductProtocol d n Z S Ω) : LiteralSample Z Ω → Fin 2 :=
  P.aligned.toBorn.reportedDecision ∘ sampleEquiv.{u,v,w}
def Legal (P : OriginalProductProtocol d n Z S Ω) (p : LiteralSample Z Ω) : Prop :=
  MeasurableExecution.Legal P.aligned.toRawRules (sampleEquiv.{u,v,w} p)
def Capped (P : OriginalProductProtocol d n Z S Ω) (N : ℕ) : Prop :=
  ∀ p, P.Legal p → P.time p ≤ (N : ℕ∞)

theorem time_measurable (P : OriginalProductProtocol d n Z S Ω) : Measurable P.time :=
  P.aligned.toBorn.time_measurable.comp sampleEquiv.measurable
theorem reportedDecision_measurable (P : OriginalProductProtocol d n Z S Ω) : Measurable P.reportedDecision :=
  P.aligned.toBorn.reportedDecision_measurable.comp sampleEquiv.measurable

def fullRecord (P : OriginalProductProtocol d n Z S Ω) :
    LiteralSample Z Ω → Z × (ℕ → Unit ⊕ (S × ((i : Fin n) → Ω i))) :=
  fullSampleEquiv.{u,v,w}.symm ∘ fullRecordSample P.aligned.toRawRules ∘ sampleEquiv.{u,v,w}

omit [NeZero d] in
theorem fullRecord_measurable (P : OriginalProductProtocol d n Z S Ω) : Measurable P.fullRecord :=
  fullSampleEquiv.symm.measurable.comp ((fullRecordSample_measurable P.aligned.toRawRules).comp
    sampleEquiv.measurable)

omit [NeZero d] in
theorem fullRecord_seed (P : OriginalProductProtocol d n Z S Ω) (p : LiteralSample Z Ω) :
    (P.fullRecord p).1 = p.1 := rfl

omit [NeZero d] in
theorem fullRecord_recovers (P : OriginalProductProtocol d n Z S Ω) (p : LiteralSample Z Ω)
    (hp : P.Legal p) (m : ℕ) : Sum.map id Prod.snd ((P.fullRecord p).2 m) = p.2 m := by
  have h := fullRecordSample_recovers P.aligned.toRawRules (sampleEquiv.{u,v,w} p) hp m
  have hm := congrArg (Sum.map id (fun x => fun i => (x i).down)) h
  convert hm using 1
  · change Sum.map id Prod.snd (Sum.map id (fun r => (r.1.down, fun i => (r.2 i).down))
      ((fullRecordSample P.aligned.toRawRules (sampleEquiv.{u,v,w} p)).2 m)) = _
    cases (fullRecordSample P.aligned.toRawRules (sampleEquiv.{u,v,w} p)).2 m <;> rfl
  · change p.2 m = Sum.map id (fun x => fun i => (x i).down)
      (Sum.map id (fun x => fun i => ULift.up (x i)) (p.2 m))
    cases p.2 m <;> rfl

theorem capped_iff (P : OriginalProductProtocol d n Z S Ω) (N : ℕ) :
    P.aligned.toBorn.Capped N ↔ P.Capped N := by
  constructor
  · intro h p hp
    exact h (sampleEquiv.{u,v,w} p) hp
  · intro h p hp
    obtain ⟨q, rfl⟩ := sampleEquiv.{u,v,w}.surjective p
    exact h q hp

def literalPrefix (m : ℕ) (p : LiteralSample Z Ω) : Z × (Fin m → Unit ⊕ ((i : Fin n) → Ω i)) :=
  (p.1, fun i => p.2 i)

theorem literalPrefix_measurable (m : ℕ) : Measurable (literalPrefix (Z := Z) (Ω := Ω) m) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr (fun i => (measurable_pi_apply i.val).comp measurable_snd))

def unliftPrefix (m : ℕ)
    (h : History (ULift.{max u v w} Z) ((i : Fin n) → ULift.{max u v w} (Ω i)) m) :
    Z × (Fin m → Unit ⊕ ((i : Fin n) → Ω i)) :=
  ((prefixSeed m h).down, fun i => Sum.map id (fun x k => (x k).down) (prefixRecord m h i))

theorem unliftPrefix_measurable (m : ℕ) : Measurable (unliftPrefix.{u,v,w} (Z := Z) (Ω := Ω) m) := by
  apply (measurable_down.comp (prefixSeed_measurable m)).prodMk
  apply measurable_pi_iff.mpr
  intro i
  apply (measurable_id.sumMap (measurable_pi_iff.mpr
    (fun k => measurable_down.comp (measurable_pi_apply k)))).comp
  exact prefixRecord_measurable m i

theorem unliftPrefix_rawPrefix (m : ℕ)
    (p : Sample (ULift.{max u v w} Z) (Slot ((i : Fin n) → ULift.{max u v w} (Ω i)))) :
    unliftPrefix.{u,v,w} m (rawPrefix m p) = literalPrefix m (sampleEquiv.{u,v,w}.symm p) := by
  apply Prod.ext
  · exact congrArg ULift.down (prefixSeed_rawPrefix m p)
  funext i
  change Sum.map id (fun x k => (x k).down) (prefixRecord m (rawPrefix m p) i) = _
  rw [prefixRecord_rawPrefix]
  rfl

theorem law_prefix (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    (P.law ρ).map (literalPrefix m) =
      (prefixLaw P.aligned.seedLaw (P.aligned.toBorn.kernel ρ) m).map (unliftPrefix.{u,v,w} m) := by
  change (P.law ρ).map (literalPrefix m) =
    (prefixLaw P.aligned.toBorn.seedLaw (P.aligned.toBorn.kernel ρ) m).map (unliftPrefix.{u,v,w} m)
  rw [law, Measure.map_map (literalPrefix_measurable m) sampleEquiv.{u,v,w}.symm.measurable,
    ← P.aligned.toBorn.law_prefix ρ m,
    Measure.map_map (unliftPrefix_measurable.{u,v,w} m) (rawPrefix_measurable m)]
  congr 1
  funext p
  exact (unliftPrefix_rawPrefix.{u,v,w} m p).symm

def copyCost (P : OriginalProductProtocol d n Z S Ω) (p : LiteralSample Z Ω) : ℝ≥0∞ :=
  ENat.toENNReal (P.time p)

theorem copyCost_measurable (P : OriginalProductProtocol d n Z S Ω) : Measurable P.copyCost :=
  (measurable_of_countable ENat.toENNReal).comp P.time_measurable

def expectedCopies (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : ℝ≥0∞ := ∫⁻ p, P.copyCost p ∂P.law ρ

theorem expectedCopies_eq_aligned (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    P.expectedCopies ρ = P.aligned.toBorn.expectedCopies ρ := by
  rw [expectedCopies, law, lintegral_map P.copyCost_measurable sampleEquiv.symm.measurable]
  apply lintegral_congr
  intro p
  change ENat.toENNReal (P.aligned.toBorn.time
    (sampleEquiv.{u,v,w} (sampleEquiv.{u,v,w}.symm p))) = _
  rw [sampleEquiv.apply_symm_apply]
  rfl

theorem expected_min (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    (∑ i ∈ Finset.range m, prefixLaw P.aligned.seedLaw (P.aligned.toBorn.kernel ρ) i
      (active P.aligned.toRawRules i)) = ∫⁻ p, min (P.copyCost p) (m : ℝ≥0∞) ∂P.law ρ := by
  calc
    _ = ∫⁻ p, min (P.aligned.toBorn.copyCost p) (m : ℝ≥0∞) ∂P.aligned.toBorn.law ρ :=
      P.aligned.toBorn.expected_min ρ m
    _ = _ := ?_
  rw [law, lintegral_map (P.copyCost_measurable.min measurable_const) sampleEquiv.{u,v,w}.symm.measurable]
  apply lintegral_congr
  intro p
  change min _ _ = min (ENat.toENNReal (P.aligned.toBorn.time
    (sampleEquiv.{u,v,w} (sampleEquiv.{u,v,w}.symm p)))) _
  rw [sampleEquiv.apply_symm_apply]
  rfl

def Terminates (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : Prop := ∀ᵐ p ∂P.law ρ, P.time p ≠ ⊤

theorem terminates_iff_aligned (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    P.Terminates ρ ↔ P.aligned.toBorn.Terminates ρ := by
  unfold Terminates BornProtocol.Terminates
  have hm : MeasurableSet {p | P.time p ≠ ⊤} :=
    (P.time_measurable (measurableSet_singleton ⊤)).compl
  rw [law, ae_map_iff sampleEquiv.{u,v,w}.symm.measurable.aemeasurable hm]
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall (fun p => by
    change (P.aligned.toBorn.time (sampleEquiv.{u,v,w} (sampleEquiv.{u,v,w}.symm p)) ≠ ⊤) ↔ _
    rw [sampleEquiv.apply_symm_apply])

theorem decision_measure (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : Fin 2) :
    P.law ρ {p | P.reportedDecision p = j} =
      P.aligned.toBorn.law ρ {p | P.aligned.toBorn.reportedDecision p = j} := by
  have hm : MeasurableSet {p | P.reportedDecision p = j} :=
    P.reportedDecision_measurable (measurableSet_singleton j)
  rw [law, Measure.map_apply sampleEquiv.{u,v,w}.symm.measurable hm]
  congr 1
  ext p
  change P.aligned.toBorn.reportedDecision (sampleEquiv.{u,v,w} (sampleEquiv.{u,v,w}.symm p)) = j ↔ _
  rw [sampleEquiv.apply_symm_apply]
  rfl

def Valid (P : OriginalProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : Prop :=
  (∀ ρ, a ≤ pureTargetFidelity ψ ρ →
    P.Terminates ρ ∧ P.law ρ {p | P.reportedDecision p = 1} ≤ ENNReal.ofReal δ) ∧
  (∀ ρ, pureTargetFidelity ψ ρ ≤ b →
    P.Terminates ρ ∧ P.law ρ {p | P.reportedDecision p = 0} ≤ ENNReal.ofReal δ)

theorem valid_iff_aligned (P : OriginalProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    P.Valid ψ a b δ ↔ P.aligned.toBorn.Valid ψ a b δ := by
  constructor
  · rintro ⟨hh, hl⟩
    constructor
    · intro ρ hρ
      obtain ⟨ht, he⟩ := hh ρ hρ
      refine ⟨(P.terminates_iff_aligned ρ).mp ht, ?_⟩
      rw [← P.decision_measure ρ 1]
      exact he
    · intro ρ hρ
      obtain ⟨ht, he⟩ := hl ρ hρ
      refine ⟨(P.terminates_iff_aligned ρ).mp ht, ?_⟩
      rw [← P.decision_measure ρ 0]
      exact he
  · rintro ⟨hh, hl⟩
    constructor
    · intro ρ hρ
      obtain ⟨ht, he⟩ := hh ρ hρ
      refine ⟨(P.terminates_iff_aligned ρ).mpr ht, ?_⟩
      rw [P.decision_measure ρ 1]
      exact he
    · intro ρ hρ
      obtain ⟨ht, he⟩ := hl ρ hρ
      refine ⟨(P.terminates_iff_aligned ρ).mpr ht, ?_⟩
      rw [P.decision_measure ρ 0]
      exact he

theorem capped_terminates (P : OriginalProductProtocol d n Z S Ω) (N : ℕ) (h : P.Capped N)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : P.Terminates ρ :=
  (P.terminates_iff_aligned ρ).mpr (P.aligned.toBorn.capped_terminates N ((P.capped_iff N).mpr h) ρ)

theorem capped_expectedCopies (P : OriginalProductProtocol d n Z S Ω) (N : ℕ) (h : P.Capped N)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : P.expectedCopies ρ ≤ (N : ℝ≥0∞) := by
  rw [P.expectedCopies_eq_aligned]
  exact P.aligned.toBorn.capped_expectedCopies N ((P.capped_iff N).mpr h) ρ

theorem expected_truncations (P : OriginalProductProtocol d n Z S Ω)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (⨆ m : ℕ, ∫⁻ p, min (P.copyCost p) (m : ℝ≥0∞) ∂P.law ρ) = P.expectedCopies ρ :=
  LocalCertification.Information.KernelTerminal.expected_truncations (P.law ρ) P.copyCost P.copyCost_measurable

end OriginalProductProtocol
variable {d n : ℕ} [NeZero d]
  {Z : Type u} {S : Type v} {Ω : Fin n → Type w}
  [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]

theorem exists_original_universe_execution (P : RawProtocol Z S ((i : Fin n) → Ω i))
    (M : ∀ i, POVMKernel S (Ω i) (Fin d)) :
    ∃ Q : ProductProtocol d n (ULift.{max u v w} Z) (ULift.{max u v w} S)
        (fun i => ULift.{max u v w} (Ω i)),
    ∃ e : (Z × (ℕ → Unit ⊕ ((i : Fin n) → Ω i))) ≃ᵐ
        Sample (ULift.{max u v w} Z) (Slot ((i : Fin n) → ULift.{max u v w} (Ω i))),
      Q.seedLaw = P.seedLaw.map ULift.up ∧
      (∀ m z h, Q.rule m (z, h) = Sum.map id ULift.up
        (P.rule m (z.down, fun i => ((h i).1.down, fun k => ((h i).2 k).down)))) ∧
      (∀ i s, (Q.localFamilies i).measurement s =
        ((M i).measurement s.down).map ULift.up measurable_up) ∧
      (∀ p, (e p).1 = ULift.up p.1 ∧
        ∀ m, (e p).2 m = Sum.map id (fun x i => ULift.up (x i)) (p.2 m)) ∧
      (∀ ρ s, Q.toBorn.measurements.bornKernel ρ (ULift.up s) =
        ((MeasurablePOVM.product (fun i => (M i).measurement s)).born ρ).map
          (fun x i => ULift.up (x i))) ∧
    ∃ law : QIT.State (CertificationGaussian.QuditIndex d n) →
        Measure (Z × (ℕ → Unit ⊕ ((i : Fin n) → Ω i))),
    ∃ T : (Z × (ℕ → Unit ⊕ ((i : Fin n) → Ω i))) → ℕ∞,
    ∃ D : (Z × (ℕ → Unit ⊕ ((i : Fin n) → Ω i))) → Fin 2,
    ∃ F : (Z × (ℕ → Unit ⊕ ((i : Fin n) → Ω i))) →
        Z × (ℕ → Unit ⊕ (S × ((i : Fin n) → Ω i))),
      (∀ ρ, IsProbabilityMeasure (law ρ)) ∧ Measurable T ∧ Measurable D ∧
      Measurable F ∧
      (∀ p, F p =
        (((fullRecordSample Q.toRawRules (e p)).1).down, fun m =>
          Sum.map id (fun r => (r.1.down, fun i => (r.2 i).down))
            ((fullRecordSample Q.toRawRules (e p)).2 m))) ∧
      (∀ p, (F p).1 = p.1) ∧
      (∀ p, Legal Q.toRawRules (e p) → ∀ m, Sum.map id Prod.snd ((F p).2 m) = p.2 m) ∧
      (∀ ρ, law ρ = (Q.toBorn.law ρ).map e.symm) ∧
      (∀ p, T p = Q.toBorn.time (e p) ∧ D p = Q.toBorn.reportedDecision (e p)) ∧
      (∀ ρ m, (law ρ).map (fun p => (p.1, fun i : Fin m => p.2 i)) =
        (prefixLaw Q.seedLaw (Q.toBorn.kernel ρ) m).map (fun h =>
          ((prefixSeed m h).down, fun i : Fin m =>
            Sum.map id (fun x k => (x k).down) (prefixRecord m h i)))) ∧
      (∀ N, Q.toBorn.Capped N ↔ ∀ p, Legal Q.toRawRules (e p) → T p ≤ (N : ℕ∞)) ∧
      (∀ ρ, Q.toBorn.expectedCopies ρ = ∫⁻ p, ENat.toENNReal (T p) ∂law ρ) ∧
      (∀ ρ m, (∑ i ∈ Finset.range m,
        prefixLaw Q.seedLaw (Q.toBorn.kernel ρ) i (active Q.toRawRules i)) =
          ∫⁻ p, min (ENat.toENNReal (T p)) (m : ℝ≥0∞) ∂law ρ) ∧
      (∀ ψ a b δ, Q.toBorn.Valid ψ a b δ ↔
        (∀ ρ, a ≤ pureTargetFidelity ψ ρ →
          (∀ᵐ p ∂law ρ, T p ≠ ⊤) ∧ law ρ {p | D p = 1} ≤ ENNReal.ofReal δ) ∧
        (∀ ρ, pureTargetFidelity ψ ρ ≤ b →
          (∀ᵐ p ∂law ρ, T p ≠ ⊤) ∧ law ρ {p | D p = 0} ≤ ENNReal.ofReal δ)) := by
  let R : OriginalProductProtocol d n Z S Ω := { toRawProtocol := P, localFamilies := M }
  refine ⟨R.aligned, OriginalProductProtocol.sampleEquiv.{u,v,w}, rfl,
    (fun _ _ _ => rfl), (fun _ _ => rfl), (fun _ => ⟨rfl, fun _ => rfl⟩),
    R.aligned_kernel, R.law, R.time, R.reportedDecision, R.fullRecord,
    (fun _ => inferInstance), R.time_measurable, R.reportedDecision_measurable,
    R.fullRecord_measurable, (fun _ => rfl), R.fullRecord_seed, R.fullRecord_recovers,
    (fun _ => rfl), (fun _ => ⟨rfl, rfl⟩), R.law_prefix, R.capped_iff,
    (fun ρ => (R.expectedCopies_eq_aligned ρ).symm), R.expected_min, ?_⟩
  intro ψ a b δ
  exact (R.valid_iff_aligned ψ a b δ).symm
end LocalCertification.Protocol.MeasurableExecution
