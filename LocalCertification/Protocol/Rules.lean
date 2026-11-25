import LocalCertification.Information.FiniteHistoryKL

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w

/-- Stop carries the actual decision (0 accepts high fidelity); Continue chooses the full setting. -/
abbrev Action (S : Type v) := Fin 2 ⊕ S

/-- Public measurement records retain the whole setting label and the complete outcome. -/
abbrev Record (S : Type v) (O : Type w) := S × O

/-- Causal rules on all seed/full-record histories. There is no unknown-state argument.
The seed may inhabit an arbitrary universe and arbitrary measurable space. -/
structure RawRules (Z : Type u) (S : Type v) (O : Type w)
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O] where
  rule : (t : ℕ) → Z × (Fin t → Record S O) → Action S
  measurable_rule : ∀ t, Measurable (rule t)

/-- A common source-independent seed law together with the complete causal rules. -/
structure RawProtocol (Z : Type u) (S : Type v) (O : Type w)
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O] extends RawRules Z S O where
  seedLaw : Measure Z
  seed_probability : IsProbabilityMeasure seedLaw

instance rawProtocol_seed_probability {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O] (P : RawProtocol Z S O) :
    IsProbabilityMeasure P.seedLaw := P.seed_probability

/-- Empty padding uses a sum, with its standard coproduct sigma algebra even for continuous labels. -/
abbrev PaddedRecord (S : Type v) (O : Type w) := Unit ⊕ Record S O

/-- At a fixed slot horizon we retain every padded full record and the already computed next action. -/
abbrev ExecutionState (S : Type v) (O : Type w) (m : ℕ) :=
  (Fin m → PaddedRecord S O) × Action S

variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]

/-- The continuation predicate is a measurable coproduct branch, not a test on quantum input. -/
def actionContinues : Action S → Bool := Sum.elim (fun _ => false) (fun _ => true)

theorem actionContinues_measurable : Measurable (actionContinues (S := S)) :=
  measurable_const.sumElim measurable_const

/-- A default is only used to totalize inactive or inconsistent prefixes. -/
def actionSetting [Inhabited S] : Action S → S := Sum.elim (fun _ => default) id

theorem actionSetting_measurable [Inhabited S] : Measurable (actionSetting (S := S)) :=
  measurable_const.sumElim measurable_id

def actionDecision : Action S → Fin 2 := Sum.elim id (fun _ => 0)

theorem actionDecision_measurable : Measurable (actionDecision (S := S)) :=
  measurable_id.sumElim measurable_const

def paddedRecordValue [Inhabited S] [Inhabited O] : PaddedRecord S O → Record S O :=
  Sum.elim (fun _ => default) id

theorem paddedRecordValue_measurable [Inhabited S] [Inhabited O] :
    Measurable (paddedRecordValue (S := S) (O := O)) := measurable_const.sumElim measurable_id

/-- Appending the actual final coordinate preserves measurability of finite full histories. -/
theorem measurable_fin_snoc {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] {m : ℕ}
    {f : A → Fin m → B} {g : A → B} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => Fin.snoc (α := fun _ : Fin (m + 1) => B) (f a) (g a)) := by
  apply measurable_pi_iff.mpr
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hg
  | cast i => simpa only [Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply i).comp hf

/-- Initial rules may stop immediately, before any copy is measured. -/
def initialState (R : RawRules Z S O) (z : Z) : ExecutionState S O 0 :=
  (Fin.elim0, R.rule 0 (z, Fin.elim0))

theorem initialState_measurable (R : RawRules Z S O) : Measurable (initialState R) :=
  measurable_const.prodMk ((R.measurable_rule 0).comp (measurable_id.prodMk measurable_const))

end LocalCertification.Protocol
