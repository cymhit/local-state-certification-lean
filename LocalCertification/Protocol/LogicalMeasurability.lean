import LocalCertification.Protocol.StoppingTime
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.ENNReal.ENatENNReal

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- Causal logical execution is measurable on the original seed/stream product sigma algebra. -/
theorem logicalPrefix_measurable (R : RawRules Z S O) (m : ℕ) :
    Measurable (fun p : Z × (ℕ → O) => logicalPrefix R p.1 p.2 m) := by
  induction m with
  | zero => exact measurable_up.comp measurable_fst
  | succ m ih =>
    have hc : MeasurableSet {p : Z × (ℕ → O) | runContinues R p.1 p.2 m} :=
      (actionContinues_measurable.comp (measurable_snd.comp ((execPrefix_measurable R m).comp ih)))
        (measurableSet_singleton true)
    exact ih.prodMk (Measurable.ite hc
      ((measurable_of_countable Option.some).comp ((measurable_pi_apply m).comp measurable_snd))
      measurable_const)

theorem runState_measurable (R : RawRules Z S O) (m : ℕ) :
    Measurable (fun p : Z × (ℕ → O) => runState R p.1 p.2 m) :=
  (execPrefix_measurable R m).comp (logicalPrefix_measurable R m)

theorem runContinues_measurableSet (R : RawRules Z S O) (m : ℕ) :
    MeasurableSet {p : Z × (ℕ → O) | runContinues R p.1 p.2 m} :=
  (actionContinues_measurable.comp (measurable_snd.comp (runState_measurable R m)))
    (measurableSet_singleton true)

/-- First stopping time is measurable with infinity retained, without completing or shrinking the seed space. -/
theorem stoppingTime_measurable (R : RawRules Z S O) :
    Measurable (fun p : Z × (ℕ → O) => stoppingTime R p.1 p.2) := by
  apply measurable_of_Iic
  intro t
  cases t with
  | top => simp
  | coe m =>
    change MeasurableSet {p : Z × (ℕ → O) | stoppingTime R p.1 p.2 ≤ (m : WithTop ℕ)}
    simp only [stoppingTime_le_iff]
    change MeasurableSet ({p : Z × (ℕ → O) | runContinues R p.1 p.2 m}ᶜ)
    exact (runContinues_measurableSet R m).compl

/-- The terminal decision, including its fixed value on nontermination, is measurable. -/
theorem terminalDecision_measurable (R : RawRules Z S O) :
    Measurable (fun p : Z × (ℕ → O) => terminalDecision R p.1 p.2) := by
  apply measurable_to_countable'
  intro j
  have he : {p : Z × (ℕ → O) | terminalDecision R p.1 p.2 = j} =
      {p | stoppingTime R p.1 p.2 = ⊤ ∧ j=0} ∪
        ⋃ m : ℕ, {p | ¬runContinues R p.1 p.2 m ∧ actionDecision (runState R p.1 p.2 m).2 = j} := by
    ext p
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    constructor
    · intro hp
      by_cases h : ∃ m, ¬runContinues R p.1 p.2 m
      · right
        obtain ⟨m,hm⟩ := h
        exact ⟨m,hm,(terminalDecision_eq_of_stopped R p.1 p.2 m hm).symm.trans hp⟩
      · left
        refine ⟨(stoppingTime_eq_top_iff R p.1 p.2).mpr (fun m => not_not.mp (not_exists.mp h m)), ?_⟩
        simpa only [terminalDecision, dite_eq_right h] using hp.symm
    · rintro (⟨ht,hj⟩ | ⟨m,hm,hj⟩)
      · have h : ¬∃ m, ¬runContinues R p.1 p.2 m := by
          intro hn
          obtain ⟨m,hm⟩ := hn
          exact hm ((stoppingTime_eq_top_iff R p.1 p.2).mp ht m)
        simp only [terminalDecision, dite_eq_right h, hj]
      · exact (terminalDecision_eq_of_stopped R p.1 p.2 m hm).trans hj
  change MeasurableSet {p : Z × (ℕ → O) | terminalDecision R p.1 p.2 = j}
  rw [he]
  apply MeasurableSet.union
  · exact ((stoppingTime_measurable R) (measurableSet_singleton ⊤)).inter (by
      by_cases h : j=0
      · simp only [h]; exact MeasurableSet.univ
      · simp only [h]; exact MeasurableSet.empty)
  · exact MeasurableSet.iUnion (fun m => (runContinues_measurableSet R m).compl.inter
      ((actionDecision_measurable.comp (measurable_snd.comp (runState_measurable R m)))
        (measurableSet_singleton j)))

omit [Fintype O] [MeasurableSingletonClass O] in
/-- The standard ENat-to-ENNReal embedding preserves the exact truncated-copy identity. -/
theorem runCopyCount_ennreal_min (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    (runCopyCount R z x m : ℝ≥0∞) = min (ENat.toENNReal (stoppingTime R z x)) (m : ℝ≥0∞) := by
  have hn : (runCopyCount R z x m : ℕ∞) = min (show ℕ∞ from stoppingTime R z x) (m : ℕ∞) :=
    runCopyCount_eq_min_stoppingTime R z x m
  have h := (congrArg ENat.toENNReal hn).trans (ENat.toENNReal_min (show ℕ∞ from stoppingTime R z x) (m : ℕ∞))
  simpa only [ENat.toENNReal_coe] using h

end LocalCertification.Protocol
