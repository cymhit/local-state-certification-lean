import LocalCertification.Protocol.BehaviorTree

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- Tree execution preserves every full setting/outcome record and action, for every seed and stream. -/
theorem treeRules_runState_eq (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    runState (treeRules (seedTreeImage R)) (seedToTree R z) x m = runState R z x m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hm : runContinues R z x m
    · have hc : runContinues (treeRules (seedTreeImage R)) (seedToTree R z) x m := by
        simpa only [runContinues, ih] using hm
      rw [runState_succ_active _ _ _ m hc, runState_succ_active R z x m hm]
      simp only [appendOutcome, ih]
      apply Prod.ext
      · rfl
      · change treeOfSeed R z (List.ofFn (fun i =>
          (Fin.snoc (α := fun _ : Fin (m+1) => Record S O) (fun i => paddedRecordValue ((runState R z x m).1 i))
            (actionSetting (runState R z x m).2, x m) i).2)) = _
        have hw : (fun i : Fin (m+1) =>
            (Fin.snoc (α := fun _ : Fin (m+1) => Record S O) (fun i => paddedRecordValue ((runState R z x m).1 i))
              (actionSetting (runState R z x m).2, x m) i).2) = (fun i : Fin (m+1) => x i) := by
          funext i
          cases i using Fin.lastCases with
          | last => simp only [Fin.snoc_last, Fin.val_last]
          | cast i => simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using runState_outcomes_live R z x m hm i
        rw [hw]
        change treeOfSeed R z (wordOfStream x (m+1)) = _
        rw [treeOfSeed_on_stream, runState_succ_active R z x m hm]
        rfl
    · have hc : ¬runContinues (treeRules (seedTreeImage R)) (seedToTree R z) x m := by
        simpa only [runContinues, ih] using hm
      rw [runState_succ_stopped _ _ _ m hc, runState_succ_stopped R z x m hm, ih]

/-- The initial seed may be collapsed to its tree, but the pointwise stopping time is unchanged. -/
theorem treeRules_stoppingTime_eq (R : RawRules Z S O) (z : Z) (x : ℕ → O) :
    stoppingTime (treeRules (seedTreeImage R)) (seedToTree R z) x = stoppingTime R z x := by
  have hr : runState (treeRules (seedTreeImage R)) (seedToTree R z) x = runState R z x :=
    funext (treeRules_runState_eq R z x)
  unfold stoppingTime runContinues
  rw [hr]

theorem treeRules_terminalDecision_eq (R : RawRules Z S O) (z : Z) (x : ℕ → O) :
    terminalDecision (treeRules (seedTreeImage R)) (seedToTree R z) x = terminalDecision R z x := by
  have hr : runState (treeRules (seedTreeImage R)) (seedToTree R z) x = runState R z x :=
    funext (treeRules_runState_eq R z x)
  unfold terminalDecision runContinues
  rw [hr]

/-- Surjectivity onto the entire image preserves caps on all branches, including all null seeds. -/
theorem treeRules_everyPathCap_iff (R : RawRules Z S O) (N : ℕ) :
    EveryPathCap (treeRules (seedTreeImage R)) N ↔ EveryPathCap R N := by
  constructor
  · intro h z x
    simpa only [runContinues, treeRules_runState_eq] using h (seedToTree R z) x
  · intro h t x
    obtain ⟨z,rfl⟩ := seedToTree_surjective R t
    simpa only [runContinues, treeRules_runState_eq] using h z x

omit [Fintype O] [MeasurableSingletonClass O] in
/-- Generated trees repeat the same stop on every descendant along every full outcome stream. -/
theorem treeOfSeed_absorbing (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m k : ℕ)
    (hm : ¬runContinues R z x m) :
    treeOfSeed R z (wordOfStream x (m+k)) = treeOfSeed R z (wordOfStream x m) := by
  rw [treeOfSeed_on_stream, treeOfSeed_on_stream]
  exact runState_action_after_stop R z x m hm k

end LocalCertification.Protocol
