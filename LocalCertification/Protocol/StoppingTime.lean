import LocalCertification.Protocol.LogicalRun

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O]

/-- The first stopping time is infinity on nonterminating runs, and may be zero. -/
def stoppingTime (R : RawRules Z S O) (z : Z) (x : ℕ → O) : WithTop ℕ := by
  classical
  exact if h : ∃ m, ¬runContinues R z x m then (Nat.find h : WithTop ℕ) else ⊤

/-- The terminal decision is total, with a fixed value on nonterminating runs. -/
def terminalDecision (R : RawRules Z S O) (z : Z) (x : ℕ → O) : Fin 2 := by
  classical
  exact if h : ∃ m, ¬runContinues R z x m then
    actionDecision (runState R z x (Nat.find h)).2 else 0

theorem stoppingTime_le_iff (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    stoppingTime R z x ≤ (m : WithTop ℕ) ↔ ¬runContinues R z x m := by
  classical
  by_cases h : ∃ m, ¬runContinues R z x m
  · simp only [stoppingTime, dite_eq_left h, Nat.cast_le]
    constructor
    · intro hle ha
      exact Nat.find_spec h (runContinues_antitone R z x hle ha)
    · exact fun hm => Nat.find_min' h hm
  · simp only [stoppingTime, dite_eq_right h]
    exact iff_of_false (not_le_of_gt (WithTop.natCast_lt_top m)) (not_exists.mp h m)

theorem stoppingTime_eq_top_iff (R : RawRules Z S O) (z : Z) (x : ℕ → O) :
    stoppingTime R z x = ⊤ ↔ ∀ m, runContinues R z x m := by
  classical
  by_cases h : ∃ m, ¬runContinues R z x m
  · simp only [stoppingTime, dite_eq_left h, WithTop.natCast_ne_top, false_iff]
    exact fun ha => Nat.find_spec h (ha (Nat.find h))
  · simp only [stoppingTime, dite_eq_right h, true_iff]
    exact fun m => not_not.mp (not_exists.mp h m)

theorem runCopyCount_eq_min_find (R : RawRules Z S O) (z : Z) (x : ℕ → O)
    (h : ∃ m, ¬runContinues R z x m) (m : ℕ) :
    runCopyCount R z x m = min (Nat.find h) m := by
  induction m with
  | zero => simp [runCopyCount]
  | succ m ih =>
    by_cases hlt : m < Nat.find h
    · have ha : runContinues R z x m := not_not.mp (Nat.find_min h hlt)
      rw [runCopyCount, ih, ite_eq_left ha]
      omega
    · have hs : ¬runContinues R z x m := by
        intro ha
        exact Nat.find_spec h (runContinues_antitone R z x (Nat.le_of_not_gt hlt) ha)
      rw [runCopyCount, ih, ite_eq_right hs]
      omega

theorem runCopyCount_eq_horizon_of_never_stop (R : RawRules Z S O) (z : Z) (x : ℕ → O)
    (h : ∀ m, runContinues R z x m) (m : ℕ) : runCopyCount R z x m = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [runCopyCount, ih, ite_eq_left (h m)]

/-- Exact pathwise truncated-copy identity, including nontermination and immediate stopping. -/
theorem runCopyCount_eq_min_stoppingTime (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    (runCopyCount R z x m : WithTop ℕ) = min (stoppingTime R z x) (m : WithTop ℕ) := by
  classical
  by_cases h : ∃ m, ¬runContinues R z x m
  · rw [runCopyCount_eq_min_find R z x h m]
    simp only [stoppingTime, dite_eq_left h]
    norm_cast
  · rw [runCopyCount_eq_horizon_of_never_stop R z x
      (fun k => not_not.mp (not_exists.mp h k)) m]
    simp only [stoppingTime, dite_eq_right h, min_eq_right le_top]

/-- Every-path caps quantify over the full seed image, without deleting any null seed or null branch. -/
theorem everyPathCap_iff_stoppingTime_le (R : RawRules Z S O) (N : ℕ) :
    EveryPathCap R N ↔ ∀ z x, stoppingTime R z x ≤ (N : WithTop ℕ) := by
  simp only [EveryPathCap, stoppingTime_le_iff]

/-- On a terminated run the action at every later horizon gives the same actual terminal decision. -/
theorem terminalDecision_eq_of_stopped (R : RawRules Z S O) (z : Z) (x : ℕ → O)
    (m : ℕ) (hm : ¬runContinues R z x m) :
    terminalDecision R z x = actionDecision (runState R z x m).2 := by
  classical
  have h : ∃ k, ¬runContinues R z x k := ⟨m, hm⟩
  simp only [terminalDecision, dite_eq_left h]
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.find_min' h hm)
  rw [hk, runState_action_after_stop R z x (Nat.find h) (Nat.find_spec h) k]

end LocalCertification.Protocol
