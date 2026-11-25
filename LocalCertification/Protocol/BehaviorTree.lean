import LocalCertification.Protocol.LogicalMeasurability

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O]

/-- The small behavior tree has every finite outcome word as a coordinate, with the product sigma algebra. -/
abbrev BehaviorTree (S : Type v) (O : Type w) := List O → Action S

/-- A finite word is completed only to evaluate its already determined finite logical prefix. -/
def streamOfWord (xs : List O) (k : ℕ) : O := xs[k]?.getD default

def wordOfStream (x : ℕ → O) (m : ℕ) : List O := List.ofFn (fun i : Fin m => x i)

omit [MeasurableSpace O] in
theorem streamOfWord_wordOfStream (x : ℕ → O) (m k : ℕ) (hk : k < m) :
    streamOfWord (wordOfStream x m) k = x k := by
  simp [streamOfWord, wordOfStream, hk]

/-- Logical execution through m depends on precisely the first m outcomes, pointwise on every seed. -/
theorem logicalPrefix_congr_prefix (R : RawRules Z S O) (z : Z) (x y : ℕ → O) (m : ℕ)
    (h : ∀ k < m, x k = y k) : logicalPrefix R z x m = logicalPrefix R z y m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [logicalPrefix, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h m (Nat.lt_succ_self m)]
    rfl

theorem runState_congr_prefix (R : RawRules Z S O) (z : Z) (x y : ℕ → O) (m : ℕ)
    (h : ∀ k < m, x k = y k) : runState R z x m = runState R z y m :=
  congrArg (execPrefix R m) (logicalPrefix_congr_prefix R z x y m h)

/-- Every original seed determines a tree on all words, including zero-probability branches. -/
def treeOfSeed (R : RawRules Z S O) (z : Z) : BehaviorTree S O :=
  fun xs => (runState R z (streamOfWord xs) xs.length).2

theorem treeOfSeed_measurable [Fintype O] [MeasurableSingletonClass O] (R : RawRules Z S O) : Measurable (treeOfSeed R) := by
  apply measurable_pi_iff.mpr
  intro xs
  exact (measurable_snd.comp (runState_measurable R xs.length)).comp
    (measurable_id.prodMk measurable_const)

theorem treeOfSeed_on_stream (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    treeOfSeed R z (wordOfStream x m) = (runState R z x m).2 := by
  change (runState R z (streamOfWord (wordOfStream x m)) (wordOfStream x m).length).2 = _
  have hl : (wordOfStream x m).length = m := List.length_ofFn
  rw [hl]
  exact congrArg Prod.snd (runState_congr_prefix R z _ x m
    (fun k hk => streamOfWord_wordOfStream x m k hk))

/-- Before stopping, the outcome component of each full retained record is the original stream coordinate. -/
theorem runState_outcomes_live (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ)
    (hm : runContinues R z x m) (i : Fin m) : (paddedRecordValue ((runState R z x m).1 i)).2 = x i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    have hp := runContinues_antitone R z x (Nat.le_succ m) hm
    rw [runState_succ_active R z x m hp]
    cases i using Fin.lastCases with
    | last => simp [appendOutcome, paddedRecordValue]
    | cast i => simpa only [appendOutcome, Fin.snoc_castSucc, Fin.val_castSucc] using ih hp i

/-- Arbitrary subsets of trees are allowed as seeds; no Borel-image condition is imposed. -/
def treeRules [Fintype O] [MeasurableSingletonClass O] (R : Set (BehaviorTree S O)) : RawRules R S O where
  rule m p := p.1.val (List.ofFn (fun i => (p.2 i).2))
  measurable_rule m := by
    have he : Measurable (fun p : R × (Fin m → O) => p.1.val (List.ofFn p.2)) := by
      apply measurable_from_prod_countable_left
      intro x
      exact (measurable_pi_apply (List.ofFn x)).comp measurable_subtype_coe
    exact he.comp (measurable_fst.prodMk (measurable_pi_iff.mpr
      (fun i => measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd))))

/-- The canonical seed set is the entire image, never a support or an almost-everywhere image. -/
def seedTreeImage (R : RawRules Z S O) : Set (BehaviorTree S O) := Set.range (treeOfSeed R)

def seedToTree (R : RawRules Z S O) (z : Z) : seedTreeImage R := ⟨treeOfSeed R z, ⟨z,rfl⟩⟩

theorem seedToTree_measurable [Fintype O] [MeasurableSingletonClass O] (R : RawRules Z S O) : Measurable (seedToTree R) :=
  (treeOfSeed_measurable R).subtype_mk

theorem seedToTree_surjective (R : RawRules Z S O) : Function.Surjective (seedToTree R) := by
  rintro ⟨t,z,hz⟩
  exact ⟨z, Subtype.ext hz⟩

end LocalCertification.Protocol
