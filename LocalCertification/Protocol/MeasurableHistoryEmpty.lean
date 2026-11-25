import LocalCertification.Protocol.MeasurableHistoryLive

/-! A protocol with no continuing histories needs no local measurements.
An empty setting type preserves this case even when local outcome spaces are
empty and hence admit no normalized POVMs. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Quantum
open LocalCertification.Information.KernelHistory
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

instance emptySettingMeasurableSpace : MeasurableSpace PEmpty.{u+1} := ⊤

private theorem state_of_initial_stop {Z L O : Type u}
    [MeasurableSpace Z] [MeasurableSpace L] [MeasurableSpace O]
    (R : RawRules Z L O) (j : Z → Fin 2)
    (hj : ∀ z, R.rule 0 (z, Fin.elim0) = Sum.inl (j z))
    (t : ℕ) (h : History Z O t) : state R t h = Sum.inl (j (historySeed t h)) := by
  induction t with
  | zero =>
    change withAction Fin.elim0 (R.rule 0 (h, Fin.elim0)) = Sum.inl (j h)
    rw [hj h]
    rfl
  | succ t ih =>
    change advance R (historySeed t h.1) (state R t h.1) h.2 = _
    rw [ih]
    rfl

namespace PaperHistoryProduct
variable {d n : ℕ} [NeZero d] {Z L : Type u} {Ω : Fin n → Type u}
  [MeasurableSpace Z] [MeasurableSpace L] [∀ i, MeasurableSpace (Ω i)]
variable (P : PaperHistoryProduct d n Z L Ω)

def initialDecision (z : Z) : Fin 2 := actionDecision (P.raw.rule 0 (z, Fin.elim0))

theorem initialDecision_measurable : Measurable P.initialDecision :=
  actionDecision_measurable.comp ((P.raw.measurable_rule 0).comp
    (measurable_id.prodMk measurable_const))

/-- The empty setting space carries the unique empty family, not a fabricated
POVM on an impossible outcome space. -/
def emptyCompile : ProductProtocol d n Z PEmpty.{u+1} Ω where
  rule _ p := Sum.inl (P.initialDecision p.1)
  measurable_rule _ := measurable_inl.comp (P.initialDecision_measurable.comp measurable_fst)
  seedLaw := P.raw.seedLaw
  seed_probability := P.raw.seed_probability
  localFamilies i := {
    measurement := fun s => PEmpty.elim s
    measurable_effect := by
      intro A hA B hB
      convert MeasurableSet.empty
      ext s
      exact PEmpty.elim s }

theorem emptyCompile_state (t : ℕ) (h : History Z ((i : Fin n) → Ω i) t) :
    state P.emptyCompile.toRawRules t h = Sum.inl (P.initialDecision (historySeed t h)) :=
  state_of_initial_stop P.emptyCompile.toRawRules P.initialDecision (fun _ => rfl) t h

theorem initial_stop_of_no_live
    (hn : ¬ ∃ t, Nonempty {h // h ∈ continuingContexts P.raw.toRawRules t}) (z : Z) :
    P.raw.rule 0 (z, Fin.elim0) = Sum.inl (P.initialDecision z) := by
  cases ha : P.raw.rule 0 (z, Fin.elim0) with
  | inl j => simp only [initialDecision, ha, actionDecision, Sum.elim_inl, id_eq]
  | inr l =>
    exact False.elim (hn ⟨0, ⟨⟨(z, Fin.elim0), ⟨l, ha⟩⟩⟩⟩)

theorem emptyCompile_preserves
    (hn : ¬ ∃ t, Nonempty {h // h ∈ continuingContexts P.raw.toRawRules t}) :
    P.Preserves P.emptyCompile := by
  have hs (t : ℕ) (h : History Z ((i : Fin n) → Ω i) t) :
      state P.raw.toRawRules t h = Sum.inl (P.initialDecision (historySeed t h)) :=
    state_of_initial_stop P.raw.toRawRules P.initialDecision (P.initial_stop_of_no_live hn) t h
  have ha (t : ℕ) (h : History Z ((i : Fin n) → Ω i) t) :
      (h ∈ active P.emptyCompile.toRawRules t) ↔ h ∈ active P.raw.toRawRules t := by
    simp only [active, Set.mem_ofPred_eq, P.emptyCompile_state, hs, reduceCtorEq,
      exists_false]
  have ht (p : Sample Z (Slot ((i : Fin n) → Ω i))) :
      P.emptyCompile.toBorn.time p = P.time p := by
    have hq : P.emptyCompile.toBorn.time p = 0 := by
      apply le_antisymm _ zero_le
      apply (stoppingTime_le_iff P.emptyCompile.toRawRules p 0).mpr
      simp [PathActive, active, P.emptyCompile_state]
    have hp : P.time p = 0 := by
      apply le_antisymm _ zero_le
      apply (stoppingTime_le_iff P.raw.toRawRules p 0).mpr
      simp [PathActive, active, hs]
    exact hq.trans hp.symm
  refine ⟨?_, ht, ?_, ?_⟩
  · intro ρ
    change executionLaw P.raw.seedLaw (P.emptyCompile.toBorn.kernel ρ) = executionLaw P.raw.seedLaw (P.kernel ρ)
    congr 1
    funext t
    ext1 h
    rw [BornProtocol.kernel_apply, P.kernel_apply]
    rw [show P.emptyCompile.toBorn.toRawRules = P.emptyCompile.toRawRules from rfl]
    rw [P.emptyCompile_state, hs]
  · intro p
    have hp : stoppingTime P.raw.toRawRules p ≤ (0 : ℕ∞) := by
      apply (stoppingTime_le_iff P.raw.toRawRules p 0).mpr
      simp [PathActive, active, hs]
    have hq : stoppingTime P.emptyCompile.toRawRules p ≤ (0 : ℕ∞) := by
      apply (stoppingTime_le_iff P.emptyCompile.toRawRules p 0).mpr
      simp [PathActive, active, P.emptyCompile_state]
    change terminalDecision P.emptyCompile.toRawRules p = terminalDecision P.raw.toRawRules p
    rw [terminalDecision_of_stopped _ _ 0 hq, terminalDecision_of_stopped _ _ 0 hp,
      P.emptyCompile_state, hs]
    rfl
  · intro p
    unfold Legal SlotLegal
    simp only [ha]

/-- No continuation anywhere: an actual empty-setting executor preserves the
independently defined paper experiment, without assuming any POVM exists. -/
theorem exists_compile_of_no_live
    (hn : ¬ ∃ t, Nonempty {h // h ∈ continuingContexts P.raw.toRawRules t}) :
    ∃ Q : ProductProtocol d n Z PEmpty.{u+1} Ω, P.Preserves Q :=
  ⟨P.emptyCompile, P.emptyCompile_preserves hn⟩

end PaperHistoryProduct
end LocalCertification.Protocol.MeasurableExecution
