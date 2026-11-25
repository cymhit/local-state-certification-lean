import LocalCertification.Protocol.StoppingTime

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O]

/-- Exactly the causal padding convention: genuine outcomes at active slots, empty slots after stopping. -/
def ConsistentPrefix (R : RawRules Z S O) : (m : ℕ) → SlotHistory Z O m → Prop
  | 0 => fun _ => True
  | m+1 => fun h => ConsistentPrefix R m h.1 ∧ (h.2 ≠ none ↔ h.1 ∈ activePrefix R m)

theorem consistentPrefix_measurable [Fintype O] (R : RawRules Z S O) (m : ℕ) :
    MeasurableSet {h | ConsistentPrefix R m h} := by
  induction m with
  | zero => exact MeasurableSet.univ
  | succ m ih =>
    exact (measurable_fst ih).inter
      (((measurable_snd (measurableSet_singleton (none : Option O))).compl).iff
        (measurable_fst (activePrefix_measurable R m)))

/-- Every logical run, including every null seed and impossible-Born outcome branch, is consistent. -/
theorem logicalPrefix_consistent (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    ConsistentPrefix R m (logicalPrefix R z x m) := by
  induction m with
  | zero => trivial
  | succ m ih =>
    change ConsistentPrefix R m (logicalPrefix R z x m) ∧ _
    refine ⟨ih, ?_⟩
    change ((if runContinues R z x m then some (x m) else none) ≠ none ↔ runContinues R z x m)
    by_cases hm : runContinues R z x m
    · simp only [ite_eq_left hm, ne_eq, Option.some_ne_none, not_false_eq_true, true_iff]
      exact hm
    · simp only [ite_eq_right hm, ne_eq, not_true_eq_false, false_iff]
      exact hm

/-- Absorption implies that any currently live decoded prefix was live one slot earlier, even off support. -/
theorem execPrefix_active_predecessor (R : RawRules Z S O) {m : ℕ}
    (h : SlotHistory Z O (m+1)) (hh : h ∈ activePrefix R (m+1)) : h.1 ∈ activePrefix R m := by
  cases ha : (execPrefix R m h.1).2 with
  | inl j =>
    have he := execPrefix_absorbing R h.1 j ha h.2
    have hn : ¬h ∈ activePrefix R (m+1) := by
      change ¬actionContinues (execPrefix R (m+1) h).2 = true
      rw [show (execPrefix R (m+1) h).2 = Sum.inl j from he]
      simp [actionContinues]
    exact False.elim (hn hh)
  | inr U =>
    change actionContinues (execPrefix R m h.1).2 = true
    simp [ha, actionContinues]

/-- Defaults do not enter any live consistent history: all its past full records are genuine. -/
theorem consistentPrefix_live_records (R : RawRules Z S O) (m : ℕ) (h : SlotHistory Z O m)
    (hc : ConsistentPrefix R m h) (ha : h ∈ activePrefix R m) :
    ∀ i, ∃ y : Record S O, (execPrefix R m h).1 i = Sum.inr y := by
  induction m with
  | zero => intro i; exact Fin.elim0 i
  | succ m ih =>
    have hp := execPrefix_active_predecessor R h ha
    have hs := hc.2.mpr hp
    obtain ⟨h,o⟩ := h
    cases o with
    | none => exact False.elim (hs rfl)
    | some x =>
      have he : execPrefix R (m+1) (h,some x) =
          appendOutcome R (slotSeed m h) (execPrefix R m h) x := by
        change advance R _ _ (some x) = _
        have hp' : actionContinues (execPrefix R m h).2 = true := hp
        simp only [advance, ite_eq_left hp']
      rw [he]
      intro i
      cases i using Fin.lastCases with
      | last => exact ⟨(actionSetting (execPrefix R m h).2,x), by simp [appendOutcome]⟩
      | cast i => simpa only [appendOutcome, Fin.snoc_castSucc] using ih h hc.1 hp i

omit [Inhabited O] in
/-- The stopped kernel puts full mass on the exact next-slot consistency condition. -/
theorem stopContinue_ae_slot_consistent [Fintype O] [MeasurableSingletonClass O]
    {H : Type*} [MeasurableSpace H] (s : Set H) (hs : MeasurableSet s) (κ : Kernel H O) (h : H) :
    ∀ᵐ o ∂stopContinue s hs κ h, (o ≠ none ↔ h ∈ s) := by
  classical
  rw [stopContinue_apply]
  by_cases hh : h ∈ s
  · rw [ite_eq_left hh]
    simp only [hh, iff_true]
    apply (ae_map_iff (measurable_of_countable Option.some).aemeasurable
      ((measurableSet_singleton (none : Option O)).compl)).mpr
    exact Filter.Eventually.of_forall (fun _ => Option.some_ne_none _)
  · rw [ite_eq_right hh]
    simp only [hh, iff_false, not_not]
    simp

/-- The actual iterated stopped law is concentrated on consistent prefixes, with no state restriction. -/
theorem prefixLaw_ae_consistent [Fintype O] [MeasurableSingletonClass O]
    (R : RawRules Z S O) (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) O) [∀ m, IsMarkovKernel (κ m)] (m : ℕ) :
    ∀ᵐ h ∂prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) m,
      ConsistentPrefix R m h := by
  induction m with
  | zero => exact Filter.Eventually.of_forall (fun _ => trivial)
  | succ m ih =>
    change ∀ᵐ h ∂(prefixLaw ν
      (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) m ⊗ₘ
      stopContinue (activePrefix R m) (activePrefix_measurable R m) (κ m)), ConsistentPrefix R (m+1) h
    apply Measure.ae_compProd_of_ae_ae (consistentPrefix_measurable R (m+1))
    filter_upwards [ih] with h hh
    filter_upwards [stopContinue_ae_slot_consistent (activePrefix R m) (activePrefix_measurable R m) (κ m) h]
      with o ho
    exact ⟨hh,ho⟩

end LocalCertification.Protocol
