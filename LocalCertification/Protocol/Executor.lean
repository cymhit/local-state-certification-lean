import LocalCertification.Protocol.Rules

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O]

/-- Append empty padding, retaining the supplied action. -/
def appendEmpty {m : ℕ} (s : ExecutionState S O m) (a : Action S) : ExecutionState S O (m+1) :=
  (Fin.snoc s.1 (Sum.inl ()), a)

/-- A genuine measurement appends its full setting/outcome pair before consulting the next rule. -/
def appendOutcome (R : RawRules Z S O) {m : ℕ} (z : Z) (s : ExecutionState S O m) (x : O) :
    ExecutionState S O (m+1) :=
  (Fin.snoc s.1 (Sum.inr (actionSetting s.2, x)),
    R.rule (m+1) (z, Fin.snoc (fun i => paddedRecordValue (s.1 i)) (actionSetting s.2, x)))

/-- Causal, absorbing update. An impossible empty active slot is totalized by stopping with decision 0. -/
def advance (R : RawRules Z S O) {m : ℕ} (z : Z) (s : ExecutionState S O m) (o : Option O) :
    ExecutionState S O (m+1) :=
  if actionContinues s.2 = true then
    match o with
    | none => appendEmpty s (Sum.inl 0)
    | some x => appendOutcome R z s x
  else appendEmpty s s.2

theorem appendOutcome_measurable (R : RawRules Z S O) (m : ℕ) (x : O) :
    Measurable (fun p : Z × ExecutionState S O m => appendOutcome R p.1 p.2 x) := by
  have hr : Measurable (fun p : Z × ExecutionState S O m => p.2.1) := measurable_fst.comp measurable_snd
  have ha : Measurable (fun p : Z × ExecutionState S O m => actionSetting p.2.2) :=
    actionSetting_measurable.comp (measurable_snd.comp measurable_snd)
  have hv : Measurable (fun p : Z × ExecutionState S O m => fun i => paddedRecordValue (p.2.1 i)) :=
    measurable_pi_iff.mpr (fun i => paddedRecordValue_measurable.comp ((measurable_pi_apply i).comp hr))
  exact (measurable_fin_snoc hr (measurable_inr.comp (ha.prodMk measurable_const))).prodMk
    ((R.measurable_rule (m+1)).comp (measurable_fst.prodMk
      (measurable_fin_snoc hv (ha.prodMk measurable_const))))

theorem advance_measurable [Fintype O] (R : RawRules Z S O) (m : ℕ) :
    Measurable (fun p : (Z × ExecutionState S O m) × Option O => advance R p.1.1 p.1.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro o
  have hr : Measurable (fun p : Z × ExecutionState S O m => p.2.1) := measurable_fst.comp measurable_snd
  have ha : Measurable (fun p : Z × ExecutionState S O m => p.2.2) := measurable_snd.comp measurable_snd
  have hc : MeasurableSet {p : Z × ExecutionState S O m | actionContinues p.2.2 = true} :=
    (actionContinues_measurable.comp ha) (measurableSet_singleton true)
  cases o with
  | none =>
    exact Measurable.ite hc
      ((measurable_fin_snoc hr measurable_const).prodMk measurable_const)
      ((measurable_fin_snoc hr measurable_const).prodMk ha)
  | some x =>
    exact Measurable.ite hc (appendOutcome_measurable R m x)
      ((measurable_fin_snoc hr measurable_const).prodMk ha)

/-- Projection of the original seed never quotients away any null seed value. -/
def slotSeed : (m : ℕ) → SlotHistory Z O m → Z
  | 0 => fun h => h.down
  | m+1 => fun h => slotSeed m h.1

omit [MeasurableSpace O] [Inhabited O] in
theorem slotSeed_measurable [Fintype O] (m : ℕ) : Measurable (slotSeed (Z := Z) (O := O) m) := by
  induction m with
  | zero => exact measurable_down
  | succ m ih => exact ih.comp measurable_fst

/-- The original rules are executed on the actual retained complete records. -/
def execPrefix (R : RawRules Z S O) : (m : ℕ) → SlotHistory Z O m → ExecutionState S O m
  | 0 => fun h => initialState R h.down
  | m+1 => fun h => advance R (slotSeed m h.1) (execPrefix R m h.1) h.2

theorem execPrefix_measurable [Fintype O] (R : RawRules Z S O) (m : ℕ) :
    Measurable (execPrefix R m) := by
  induction m with
  | zero => exact (initialState_measurable R).comp measurable_down
  | succ m ih =>
    exact (advance_measurable R m).comp
      (((slotSeed_measurable m).comp measurable_fst).prodMk (ih.comp measurable_fst) |>.prodMk measurable_snd)

/-- A copy is requested precisely when the already computed action is Continue. -/
def activePrefix (R : RawRules Z S O) (m : ℕ) : Set (SlotHistory Z O m) :=
  {h | actionContinues (execPrefix R m h).2 = true}

theorem activePrefix_measurable [Fintype O] (R : RawRules Z S O) (m : ℕ) :
    MeasurableSet (activePrefix R m) :=
  (actionContinues_measurable.comp (measurable_snd.comp (execPrefix_measurable R m)))
    (measurableSet_singleton true)

/-- The full setting is chosen before the current copy's outcome; the inactive default is never sampled. -/
def prefixSetting (R : RawRules Z S O) (m : ℕ) (h : SlotHistory Z O m) : S :=
  actionSetting (execPrefix R m h).2

theorem prefixSetting_measurable [Fintype O] (R : RawRules Z S O) (m : ℕ) :
    Measurable (prefixSetting R m) :=
  actionSetting_measurable.comp (measurable_snd.comp (execPrefix_measurable R m))

/-- Absorption is pointwise, including null seeds and prefixes with impossible measurement outcomes. -/
theorem advance_stopped (R : RawRules Z S O) {m : ℕ} (z : Z) (s : ExecutionState S O m)
    (j : Fin 2) (hs : s.2 = Sum.inl j) (o : Option O) :
    advance R z s o = appendEmpty s (Sum.inl j) := by
  simp [advance, hs, actionContinues]

theorem advance_action_stopped (R : RawRules Z S O) {m : ℕ} (z : Z) (s : ExecutionState S O m)
    (j : Fin 2) (hs : s.2 = Sum.inl j) (o : Option O) : (advance R z s o).2 = Sum.inl j := by
  rw [advance_stopped R z s j hs o]
  rfl

theorem execPrefix_absorbing (R : RawRules Z S O) {m : ℕ} (h : SlotHistory Z O m)
    (j : Fin 2) (hj : (execPrefix R m h).2 = Sum.inl j) (o : Option O) :
    (execPrefix R (m+1) (h,o)).2 = Sum.inl j :=
  advance_action_stopped R _ _ j hj o

end LocalCertification.Protocol
