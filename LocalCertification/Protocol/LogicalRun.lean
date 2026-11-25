import LocalCertification.Protocol.Executor

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O]

/-- Pointwise run for every seed and every possible outcome stream, without any support restriction. -/
def logicalPrefix (R : RawRules Z S O) (z : Z) (x : ℕ → O) : (m : ℕ) → SlotHistory Z O m
  | 0 => ULift.up z
  | m+1 => let h := logicalPrefix R z x m
    (h, if actionContinues (execPrefix R m h).2 = true then some (x m) else none)

def runState (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) : ExecutionState S O m :=
  execPrefix R m (logicalPrefix R z x m)

abbrev runContinues (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) : Prop :=
  actionContinues (runState R z x m).2 = true

theorem logicalPrefix_seed (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    slotSeed m (logicalPrefix R z x m) = z := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih

theorem runState_zero (R : RawRules Z S O) (z : Z) (x : ℕ → O) :
    runState R z x 0 = initialState R z := rfl

theorem runState_succ_active (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ)
    (hm : runContinues R z x m) :
    runState R z x (m+1) = appendOutcome R z (runState R z x m) (x m) := by
  change advance R (slotSeed m (logicalPrefix R z x m)) (runState R z x m)
    (if runContinues R z x m then some (x m) else none) = _
  rw [logicalPrefix_seed, ite_eq_left hm]
  simp only [advance, runContinues] at hm ⊢
  rw [ite_eq_left hm]

theorem runState_succ_stopped (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ)
    (hm : ¬runContinues R z x m) :
    runState R z x (m+1) = appendEmpty (runState R z x m) (runState R z x m).2 := by
  change advance R (slotSeed m (logicalPrefix R z x m)) (runState R z x m)
    (if runContinues R z x m then some (x m) else none) = _
  rw [logicalPrefix_seed, ite_eq_right hm]
  simp only [advance, runContinues] at hm ⊢
  rw [ite_eq_right hm]

/-- Once stopped, every later logical action is the same decision, pointwise for all seeds. -/
theorem runState_action_after_stop (R : RawRules Z S O) (z : Z) (x : ℕ → O)
    (m : ℕ) (hm : ¬runContinues R z x m) (k : ℕ) :
    (runState R z x (m+k)).2 = (runState R z x m).2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ¬runContinues R z x (m+k) := by simpa only [runContinues, ih] using hm
    rw [Nat.add_succ, runState_succ_stopped R z x (m+k) hk]
    exact ih

theorem runContinues_antitone (R : RawRules Z S O) (z : Z) (x : ℕ → O)
    {m n : ℕ} (hmn : m ≤ n) (hn : runContinues R z x n) : runContinues R z x m := by
  by_contra hm
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h := runState_action_after_stop R z x m hm k
  exact hm (by simpa only [runContinues, h] using hn)

/-- Before stopping, all retained records are genuine records; totalization defaults are never read. -/
theorem runState_records_present (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ)
    (hm : runContinues R z x m) : ∀ i, ∃ y : Record S O, (runState R z x m).1 i = Sum.inr y := by
  induction m with
  | zero => intro i; exact Fin.elim0 i
  | succ m ih =>
    have hp := runContinues_antitone R z x (Nat.le_succ m) hm
    rw [runState_succ_active R z x m hp]
    intro i
    cases i using Fin.lastCases with
    | last => exact ⟨(actionSetting (runState R z x m).2, x m), by simp [appendOutcome]⟩
    | cast i => simpa only [appendOutcome, Fin.snoc_castSucc] using ih hp i

/-- The next action on a live run is precisely the supplied raw rule on its complete record sequence. -/
theorem runState_action_eq_rule (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ)
    (hm : runContinues R z x m) :
    (runState R z x m).2 = R.rule m (z, fun i => paddedRecordValue ((runState R z x m).1 i)) := by
  induction m with
  | zero =>
    apply congrArg (fun f => R.rule 0 (z, f))
    funext i
    exact Fin.elim0 i
  | succ m ih =>
    have hp := runContinues_antitone R z x (Nat.le_succ m) hm
    rw [runState_succ_active R z x m hp]
    apply congrArg (fun f => R.rule (m+1) (z, f))
    funext i
    cases i using Fin.lastCases <;> simp [appendOutcome, paddedRecordValue]

/-- Actual number of measurement requests, including the copy preceding a stopping decision. -/
def runCopyCount (R : RawRules Z S O) (z : Z) (x : ℕ → O) : ℕ → ℕ
  | 0 => 0
  | m+1 => runCopyCount R z x m + if runContinues R z x m then 1 else 0

theorem runCopyCount_eq_prefixActiveCount (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    prefixActiveCount (activePrefix R) m (logicalPrefix R z x m) = (runCopyCount R z x m : ℝ≥0∞) := by
  induction m with
  | zero => simp [prefixActiveCount, runCopyCount]
  | succ m ih =>
    change prefixActiveCount (activePrefix R) m (logicalPrefix R z x m) +
      (activePrefix R m).indicator (fun _ => 1) (logicalPrefix R z x m) =
      ((runCopyCount R z x m + if runContinues R z x m then 1 else 0 : ℕ) : ℝ≥0∞)
    rw [ih, Nat.cast_add]
    congr 1
    by_cases hm : runContinues R z x m
    · rw [Set.indicator_of_mem (show logicalPrefix R z x m ∈ activePrefix R m from hm), ite_eq_left hm]
      norm_num
    · rw [Set.indicator_of_notMem (show logicalPrefix R z x m ∉ activePrefix R m from hm), ite_eq_right hm]
      norm_num

/-- A bounded protocol must stop on every seed and outcome stream, including measure-zero branches. -/
def EveryPathCap (R : RawRules Z S O) (N : ℕ) : Prop :=
  ∀ z x, ¬runContinues R z x N

end LocalCertification.Protocol
