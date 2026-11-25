import LocalCertification.Protocol.MeasurableExecutionBorn

/-! Causal history annotations of settings. The original label is retained,
and the added annotation is reconstructed from the seed and past records.
All claims below hold on literal paths, including null and inconsistent paths. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open LocalCertification.Information.KernelHistory
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

abbrev HistoryContext (Z L O : Type u) := Σ t : ℕ, Z × (Fin t → L × O)
abbrev HistorySetting (Z L O : Type u) := L × HistoryContext Z L O

namespace HistoryEncoding
variable {Z L O : Type u} [MeasurableSpace Z] [MeasurableSpace L] [MeasurableSpace O]

theorem measurable_context_mk (t : ℕ) :
    Measurable (fun p : Z × (Fin t → L × O) => (⟨t, p⟩ : HistoryContext Z L O)) :=
  Measurable.of_le_map (iInf_le _ t)

theorem measurable_from_sigma {A : Type*} {B : A → Type*} {C : Type*}
    [∀ a, MeasurableSpace (B a)] [MeasurableSpace C] (f : (Σ a, B a) → C)
    (hf : ∀ a, Measurable (fun b => f ⟨a, b⟩)) : Measurable f := by
  rw [measurable_iff_le_map, Sigma.instMeasurableSpace, MeasurableSpace.map_iInf]
  apply le_iInf
  intro a
  simpa only [MeasurableSpace.map_comp, Function.comp_def] using (hf a).le_map

def eraseRecords {n : ℕ} (h : Fin n → HistorySetting Z L O × O) : Fin n → L × O :=
  fun i => ((h i).1.1, (h i).2)

theorem eraseRecords_measurable (n : ℕ) : Measurable (eraseRecords (Z := Z) (L := L) (O := O) (n := n)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_fst.comp measurable_fst).comp (measurable_pi_apply i)).prodMk
    (measurable_snd.comp (measurable_pi_apply i))

omit [MeasurableSpace Z] [MeasurableSpace L] [MeasurableSpace O] in
theorem eraseRecords_snoc {n : ℕ} (h : Fin n → HistorySetting Z L O × O)
    (s : HistorySetting Z L O) (x : O) :
    eraseRecords (Fin.snoc h (s, x)) = Fin.snoc (eraseRecords h) (s.1, x) := by
  funext i
  cases i using Fin.lastCases <;> simp [eraseRecords]

def attach {C : Type u} (c : C) : Action L → Action (L × C) :=
  Sum.map id (fun l => (l, c))

theorem attach_measurable {C : Type u} [MeasurableSpace C] :
    Measurable (fun p : C × Action L => attach p.1 p.2) := by
  have h := (measurable_inl.comp (measurable_snd : Measurable (Prod.snd : C × Fin 2 → Fin 2))).sumElim
    (measurable_inr.comp (measurable_snd.prodMk (measurable_fst : Measurable (Prod.fst : C × L → C))))
  convert h.comp (MeasurableEquiv.prodSumDistrib C (Fin 2) L).measurable using 1
  funext p
  rcases p with ⟨c, j | l⟩ <;> rfl

/-- At a continuing history, augment the actual selected original label with
the current time, seed, and original records. -/
def rules (R : RawRules Z L O) : RawRules Z (HistorySetting Z L O) O where
  rule t p := attach (⟨t, (p.1, eraseRecords p.2)⟩ : HistoryContext Z L O)
    (R.rule t (p.1, eraseRecords p.2))
  measurable_rule t := by
    have hp : Measurable (fun p : Z × (Fin t → HistorySetting Z L O × O) =>
        (p.1, eraseRecords p.2)) :=
      measurable_fst.prodMk ((eraseRecords_measurable t).comp measurable_snd)
    exact attach_measurable.comp (((measurable_context_mk t).comp hp).prodMk
      ((R.measurable_rule t).comp hp))

def eraseState {n : ℕ} : State (HistorySetting Z L O) O n → State L O n :=
  Sum.map id (fun v => (eraseRecords v.1, v.2.1))

omit [MeasurableSpace Z] [MeasurableSpace L] [MeasurableSpace O] in
theorem eraseState_withAction {n : ℕ} (h : Fin n → HistorySetting Z L O × O)
    (a : Action (HistorySetting Z L O)) :
    eraseState (withAction h a) = withAction (eraseRecords h) (Sum.map id Prod.fst a) := by
  cases a <;> rfl

omit [MeasurableSpace Z] [MeasurableSpace L] [MeasurableSpace O] in
theorem erase_attach (c : HistoryContext Z L O) (a : Action L) :
    Sum.map id Prod.fst (attach c a) = a := by
  cases a <;> rfl

theorem advance_projection (R : RawRules Z L O) {n : ℕ} (z : Z)
    (st : State (HistorySetting Z L O) O n) (o : Slot O) :
    eraseState (advance (rules R) z st o) = advance R z (eraseState st) o := by
  rcases st with j | ⟨h, s⟩
  · rfl
  rcases o with e | x
  · rfl
  change eraseState (withAction (Fin.snoc h (s, x))
    (attach _ (R.rule (n+1) (z, eraseRecords (Fin.snoc h (s, x)))))) = _
  rw [eraseState_withAction, erase_attach, eraseRecords_snoc]
  rfl

/-- Erasing the added context recovers the original state on every prefix. -/
theorem state_projection (R : RawRules Z L O) (n : ℕ) (h : History Z O n) :
    eraseState (state (rules R) n h) = state R n h := by
  induction n with
  | zero =>
    change eraseState (withAction Fin.elim0 (attach _ (R.rule 0 (h, eraseRecords Fin.elim0)))) = _
    rw [eraseState_withAction, erase_attach]
    have he : eraseRecords (Fin.elim0 : Fin 0 → HistorySetting Z L O × O) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [he]
    rfl
  | succ n ih =>
    change eraseState (advance (rules R) _ (state (rules R) n h.1) h.2) = _
    rw [advance_projection, ih]
    rfl

/-- Every live compiled setting carries exactly the available original history. -/
theorem state_context (R : RawRules Z L O) (n : ℕ) (h : History Z O n)
    (v : (Fin n → HistorySetting Z L O × O) × HistorySetting Z L O)
    (hv : state (rules R) n h = Sum.inr v) :
    v.2.2 = ⟨n, (historySeed n h, eraseRecords v.1)⟩ := by
  cases n with
  | zero =>
    change withAction Fin.elim0 (attach _ (R.rule 0 (h, eraseRecords Fin.elim0))) = Sum.inr v at hv
    cases ha : R.rule 0 (h, eraseRecords (Fin.elim0 : Fin 0 → HistorySetting Z L O × O)) with
    | inl j => simp [ha, attach, withAction] at hv
    | inr s => simp [ha, attach, withAction] at hv; subst v; rfl
  | succ n =>
    change advance (rules R) (historySeed n h.1) (state (rules R) n h.1) h.2 = Sum.inr v at hv
    cases hs : state (rules R) n h.1 with
    | inl j => simp [hs, advance] at hv
    | inr w =>
      cases ho : h.2 with
      | inl e => simp [hs, ho, advance] at hv
      | inr x =>
        rw [hs, ho] at hv
        change withAction (Fin.snoc w.1 (w.2, x))
          (attach _ (R.rule (n+1) (historySeed n h.1, eraseRecords (Fin.snoc w.1 (w.2, x))))) = Sum.inr v at hv
        cases ha : R.rule (n+1) (historySeed n h.1, eraseRecords (Fin.snoc w.1 (w.2, x))) with
        | inl j => simp [ha, attach, withAction] at hv
        | inr s => simp [ha, attach, withAction] at hv; subst v; rfl

theorem active_iff (R : RawRules Z L O) (n : ℕ) (h : History Z O n) :
    h ∈ active (rules R) n ↔ h ∈ active R n := by
  have he := state_projection R n h
  simp only [active, Set.mem_ofPred_eq]
  rw [← he]
  cases state (rules R) n h <;> simp [eraseState]

theorem time_eq (R : RawRules Z L O) (p : Sample Z (Slot O)) :
    stoppingTime (rules R) p = stoppingTime R p := by
  apply le_antisymm
  · cases ht : stoppingTime R p with
    | top => exact le_top
    | coe m =>
      apply (stoppingTime_le_iff _ _ m).mpr
      rw [show PathActive (rules R) p m ↔ PathActive R p m from active_iff R m _]
      exact (stoppingTime_le_iff R p m).mp ht.le
  · cases ht : stoppingTime (rules R) p with
    | top => exact le_top
    | coe m =>
      apply (stoppingTime_le_iff _ _ m).mpr
      rw [← show PathActive (rules R) p m ↔ PathActive R p m from active_iff R m _]
      exact (stoppingTime_le_iff _ _ m).mp ht.le

theorem decision_eq (R : RawRules Z L O) (p : Sample Z (Slot O)) :
    terminalDecision (rules R) p = terminalDecision R p := by
  cases ht : stoppingTime R p with
  | top => rw [terminalDecision_of_top R p ht, terminalDecision_of_top _ _ ((time_eq R p).trans ht)]
  | coe m =>
    rw [terminalDecision_of_stopped R p m ht.le, terminalDecision_of_stopped _ _ m
      ((time_eq R p).trans ht).le, ← state_projection R m]
    cases state (rules R) m (rawPrefix m p) <;> rfl

theorem legal_iff (R : RawRules Z L O) (p : Sample Z (Slot O)) :
    Legal (rules R) p ↔ Legal R p := by
  unfold Legal SlotLegal
  simp only [active_iff]

theorem capped_iff (R : RawRules Z L O) (N : ℕ) : Capped (rules R) N ↔ Capped R N := by
  unfold Capped
  simp only [legal_iff, time_eq]

def eraseFullSample (p : Sample Z (Unit ⊕ (HistorySetting Z L O × O))) :
    Sample Z (Unit ⊕ (L × O)) :=
  (p.1, fun n => Sum.map id (fun r => (r.1.1, r.2)) (p.2 n))

theorem eraseFullSample_measurable : Measurable (eraseFullSample (Z := Z) (L := L) (O := O)) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr (fun n =>
    (measurable_id.sumMap ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).comp
      ((measurable_pi_apply n).comp measurable_snd)))

def outcomes (p : Sample Z (Unit ⊕ (L × O))) : Sample Z (Slot O) :=
  (p.1, fun n => Sum.map id Prod.snd (p.2 n))

theorem outcomes_measurable : Measurable (outcomes (Z := Z) (L := L) (O := O)) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr (fun n =>
    (measurable_id.sumMap measurable_snd).comp ((measurable_pi_apply n).comp measurable_snd)))

theorem fullRecord_projection (R : RawRules Z L O) (p : Sample Z (Slot O)) :
    eraseFullSample (fullRecordSample (rules R) p) = fullRecordSample R p := by
  refine Prod.ext ?_ ?_
  · rfl
  funext n
  change Sum.map id _ (labelSlot (state (rules R) n (rawPrefix n p), p.2 n)) =
    labelSlot (state R n (rawPrefix n p), p.2 n)
  rw [← state_projection R n]
  cases state (rules R) n (rawPrefix n p) <;> cases p.2 n <;> rfl

/-- Original complete records determine the augmented complete records by a
measurable causal reconstruction, pointwise on every legal sample. -/
theorem fullRecord_reconstruction (R : RawRules Z L O) :
    ∃ F : Sample Z (Unit ⊕ (L × O)) → Sample Z (Unit ⊕ (HistorySetting Z L O × O)),
      Measurable F ∧ ∀ p, Legal R p →
        F (fullRecordSample R p) = fullRecordSample (rules R) p := by
  refine ⟨fullRecordSample (rules R) ∘ outcomes,
    (fullRecordSample_measurable _).comp outcomes_measurable, ?_⟩
  intro p hp
  have he : outcomes (fullRecordSample R p) = p := by
    refine Prod.ext ?_ ?_
    · rfl
    funext n
    exact fullRecordSample_recovers R p hp n
  exact congrArg (fullRecordSample (rules R)) he

/-- Forgetting labels is causal at each finite horizon. -/
def outcomePrefix : ∀ t, FullHistory Z (Unit ⊕ (L × O)) t → History Z O t
  | 0 => id
  | t+1 => fun h => (outcomePrefix t h.1, Sum.map id Prod.snd h.2)

theorem outcomePrefix_measurable (t : ℕ) :
    Measurable (outcomePrefix (Z := Z) (L := L) (O := O) t) := by
  induction t with
  | zero => exact measurable_id
  | succ t ih =>
    exact (ih.comp measurable_fst).prodMk
      ((measurable_id.sumMap measurable_snd).comp measurable_snd)

theorem outcomePrefix_recovers (R : RawRules Z L O) (p : Sample Z (Slot O))
    (hp : Legal R p) (t : ℕ) :
    outcomePrefix t (fullPrefix R t (rawPrefix t p)) = rawPrefix t p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (outcomePrefix t (fullPrefix R t (rawPrefix t p)),
      Sum.map id Prod.snd (labelSlot (state R t (rawPrefix t p), p.2 t))) =
      (rawPrefix t p, p.2 t)
    exact Prod.ext ih (labelSlot_recovers R t (rawPrefix t p) (p.2 t) (hp t))

/-- This reconstruction only reads the available t original records. -/
def reconstructPrefix (R : RawRules Z L O) (t : ℕ) :
    FullHistory Z (Unit ⊕ (L × O)) t →
      FullHistory Z (Unit ⊕ (HistorySetting Z L O × O)) t :=
  fullPrefix (rules R) t ∘ outcomePrefix t

theorem reconstructPrefix_measurable (R : RawRules Z L O) (t : ℕ) :
    Measurable (reconstructPrefix R t) :=
  (fullPrefix_measurable (rules R) t).comp (outcomePrefix_measurable t)

/-- Exact causal record reconstruction on all legal paths, including null seeds
and impossible outcome branches. This supplies both finite-history measurability
and the absence of additional information in augmented measurement settings. -/
theorem reconstructPrefix_recovers (R : RawRules Z L O) (p : Sample Z (Slot O))
    (hp : Legal R p) (t : ℕ) :
    reconstructPrefix R t (fullPrefix R t (rawPrefix t p)) =
      fullPrefix (rules R) t (rawPrefix t p) :=
  congrArg (fullPrefix (rules R) t) (outcomePrefix_recovers R p hp t)

end HistoryEncoding
end LocalCertification.Protocol.MeasurableExecution
