import LocalCertification.Protocol.TreeExecution
import LocalCertification.Protocol.TrajectoryEncoding

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w z
variable {Z : Type u} {Y : Type v} {S : Type w} {O : Type z}
    [MeasurableSpace Z] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- Change only the seed in a finite primitive prefix; every actual slot is retained. -/
def mapSlotSeed (f : Z → Y) : (m : ℕ) → SlotHistory Z O m → SlotHistory Y O m
  | 0 => fun h => ULift.up (f h.down)
  | m+1 => fun h => (mapSlotSeed f m h.1, h.2)

omit [MeasurableSpace O] [Inhabited O] [MeasurableSingletonClass O] in
theorem mapSlotSeed_measurable (f : Z → Y) (hf : Measurable f) (m : ℕ) : Measurable (mapSlotSeed (O := O) f m) := by
  induction m with
  | zero => exact measurable_up.comp (hf.comp measurable_down)
  | succ m ih => exact (ih.comp measurable_fst).prodMk measurable_snd

/-- Change the original seed while preserving the complete primitive slot stream. -/
def mapRawSeed (f : Z → Y) (p : RawSample Z O) : RawSample Y O := (f p.1,p.2)

omit [MeasurableSpace O] [Inhabited O] [MeasurableSingletonClass O] in
theorem mapRawSeed_measurable (f : Z → Y) (hf : Measurable f) : Measurable (mapRawSeed (O := O) f) :=
  (hf.comp measurable_fst).prodMk measurable_snd

omit [MeasurableSpace Z] [MeasurableSpace Y] [MeasurableSpace O] [Inhabited O] [Fintype O] [MeasurableSingletonClass O] in
theorem mapSlotSeed_rawPrefix (f : Z → Y) (m : ℕ) (p : RawSample Z O) :
    mapSlotSeed f m (rawPrefix m p) = rawPrefix m (mapRawSeed f p) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (fun h => (h,p.2 m)) ih

omit [Fintype O] [MeasurableSingletonClass O] in
/-- Every consistent finite prefix comes from a full logical stream, including zero-weight branches. -/
theorem consistentPrefix_exists_logical (R : RawRules Z S O) (m : ℕ)
    (h : SlotHistory Z O m) (hc : ConsistentPrefix R m h) :
    ∃ (z : Z) (x : ℕ → O), logicalPrefix R z x m = h := by
  classical
  induction m with
  | zero => exact ⟨h.down, fun _ => default, rfl⟩
  | succ m ih =>
    change SlotHistory Z O m × Option O at h
    obtain ⟨z,x,hx⟩ := ih h.1 hc.1
    cases ho : h.2 with
    | none =>
      have ha : h.1 ∉ activePrefix R m := by
        intro ha
        exact (hc.2.mpr ha) ho
      refine ⟨z,x,?_⟩
      change (logicalPrefix R z x m,
        if actionContinues (execPrefix R m (logicalPrefix R z x m)).2 = true then some (x m) else none) = h
      change ¬actionContinues (execPrefix R m h.1).2 = true at ha
      rw [hx, ite_eq_right ha]
      exact Prod.ext rfl ho.symm
    | some y =>
      have ha : h.1 ∈ activePrefix R m := hc.2.mp (by simp [ho])
      let x' := Function.update x m y
      have hx' : logicalPrefix R z x' m = h.1 := by
        rw [logicalPrefix_congr_prefix R z x' x m]
        · exact hx
        · intro k hk
          simp [x', Function.update_of_ne (Nat.ne_of_lt hk)]
      refine ⟨z,x',?_⟩
      change (logicalPrefix R z x' m,
        if actionContinues (execPrefix R m (logicalPrefix R z x' m)).2 = true then some (x' m) else none) = h
      change actionContinues (execPrefix R m h.1).2 = true at ha
      rw [hx', ite_eq_left ha]
      apply Prod.ext
      · rfl
      · simpa only [x', Function.update_self] using ho.symm

/-- Full-image tree normalization maps the actual primitive logical prefix, not just its action. -/
theorem treeRules_logicalPrefix_map (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    logicalPrefix (treeRules (seedTreeImage R)) (seedToTree R z) x m =
      mapSlotSeed (seedToTree R) m (logicalPrefix R z x m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (logicalPrefix (treeRules (seedTreeImage R)) (seedToTree R z) x m,
      if actionContinues (runState (treeRules (seedTreeImage R)) (seedToTree R z) x m).2 = true
        then some (x m) else none) =
      (mapSlotSeed (seedToTree R) m (logicalPrefix R z x m),
        if actionContinues (runState R z x m).2 = true then some (x m) else none)
    rw [ih, treeRules_runState_eq]

/-- Complete executor states agree on every consistent finite prefix, with no probability support assumption. -/
theorem treeRules_execPrefix_map (R : RawRules Z S O) (m : ℕ)
    (h : SlotHistory Z O m) (hc : ConsistentPrefix R m h) :
    execPrefix (treeRules (seedTreeImage R)) m (mapSlotSeed (seedToTree R) m h) = execPrefix R m h := by
  obtain ⟨z,x,rfl⟩ := consistentPrefix_exists_logical R m h hc
  rw [← treeRules_logicalPrefix_map]
  exact treeRules_runState_eq R z x m

/-- Tree image transport preserves finite consistency pointwise. -/
theorem treeRules_consistentPrefix_map (R : RawRules Z S O) (m : ℕ)
    (h : SlotHistory Z O m) (hc : ConsistentPrefix R m h) :
    ConsistentPrefix (treeRules (seedTreeImage R)) m (mapSlotSeed (seedToTree R) m h) := by
  obtain ⟨z,x,rfl⟩ := consistentPrefix_exists_logical R m h hc
  rw [← treeRules_logicalPrefix_map]
  exact logicalPrefix_consistent _ _ _ _

end LocalCertification.Protocol
