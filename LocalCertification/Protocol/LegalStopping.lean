import LocalCertification.Protocol.ConditionalBorn
import Mathlib.Probability.Process.Stopping

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- The genuine execution time is a stopping time for the uncompleted legal-history filtration. -/
theorem legal_isStoppingTime (P : QuditProtocol Z d n) :
    IsStoppingTime (legalFiltration P.toRawRules) (fun p => executionTime P p.val) :=
  legal_stopped_measurable P

/-- The next-copy request event T≥m+1 belongs to the preceding raw finite filtration. -/
theorem legal_next_copy_measurable (P : QuditProtocol Z d n) (m : ℕ) :
    MeasurableSet[legalFiltration P.toRawRules m]
      {p : legalPaths P.toRawRules | ((m+1 : ℕ) : WithTop ℕ) ≤ executionTime P p.val} := by
  have he : {p : legalPaths P.toRawRules | ((m+1 : ℕ) : WithTop ℕ) ≤ executionTime P p.val} =
      {p | (m : WithTop ℕ) < executionTime P p.val} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    cases h : executionTime P p.val with
    | top => simp only [le_top, true_iff]; exact WithTop.natCast_lt_top m
    | coe k =>
      change (((m+1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)) ↔ ((m : ℕ∞) < (k : ℕ∞))
      simp only [ENat.natCast_le_natCast, ENat.natCast_lt_natCast]
      omega
  rw [he]
  exact legal_active_measurable P m

/-- Nontermination has the fixed terminal default, pointwise rather than merely almost surely. -/
theorem executionDecision_of_time_top (P : QuditProtocol Z d n)
    (p : RawSample Z (CertificationGaussian.QuditIndex d n)) (ht : executionTime P p = ⊤) :
    executionDecision P p = 0 := by
  have hn : ¬∃ m, ¬runContinues P.toRawRules p.1 (fun k => (p.2 k).getD default) m := by
    rintro ⟨m,hm⟩
    exact hm ((stoppingTime_eq_top_iff _ _ _).mp ht m)
  simp only [executionDecision, terminalDecision, dite_eq_right hn]

/-- The terminal decision belongs to the stopped sigma algebra, including its value on infinite runs. -/
theorem legal_terminalDecision_stopped_measurable (P : QuditProtocol Z d n) :
    Measurable[(legal_isStoppingTime P).measurableSpace] (fun p => executionDecision P p.val) := by
  let : MeasurableSpace (legalPaths P.toRawRules) := (legal_isStoppingTime P).measurableSpace
  apply measurable_to_countable'
  intro j
  change MeasurableSet[(legal_isStoppingTime P).measurableSpace]
    {p : legalPaths P.toRawRules | executionDecision P p.val = j}
  apply (legal_isStoppingTime P).measurableSet _ |>.mpr
  constructor
  · have he : {p : legalPaths P.toRawRules | executionDecision P p.val = j} =
        {p | executionTime P p.val = ⊤ ∧ j=0} ∪
        ⋃ m : ℕ, {p | executionTime P p.val ≤ (m : WithTop ℕ) ∧ executionDecision P p.val = j} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion]
      constructor
      · intro hj
        by_cases ht : executionTime P p.val = ⊤
        · exact Or.inl ⟨ht,hj.symm.trans (executionDecision_of_time_top P p.val ht)⟩
        · obtain ⟨m,hm⟩ := WithTop.ne_top_iff_exists.mp ht
          exact Or.inr ⟨m,hm.ge,hj⟩
      · rintro (⟨ht,rfl⟩ | ⟨m,hm,hj⟩)
        · exact executionDecision_of_time_top P p.val ht
        · exact hj
    rw [he]
    apply MeasurableSet.union
    · exact (((legal_isStoppingTime P).measurable_iSup) (measurableSet_singleton ⊤)).inter
        (by by_cases hj : j=0 <;> simp only [hj] <;> exact MeasurableSet.const _)
    · exact MeasurableSet.iUnion (fun m => (le_iSup (fun m => legalFiltration P.toRawRules m) m) _
        (legal_stopped_decision_measurable P j m))
  · intro m
    change MeasurableSet[legalFiltration P.toRawRules m]
      {p : legalPaths P.toRawRules | executionDecision P p.val = j ∧ executionTime P p.val ≤ (m : WithTop ℕ)}
    simpa only [and_comm] using legal_stopped_decision_measurable P j m

variable {S : Type v} {O : Type w} [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- Every original seed and arbitrary outcome stream generates a legal padded path; no support restriction is used. -/
def logicalRawPath (R : RawRules Z S O) (z : Z) (x : ℕ → O) : RawSample Z O := by
  classical
  exact (z, fun m => if runContinues R z x m then some (x m) else none)

omit [Fintype O] [MeasurableSingletonClass O] in
theorem logicalRawPath_prefix (R : RawRules Z S O) (z : Z) (x : ℕ → O) (m : ℕ) :
    rawPrefix m (logicalRawPath R z x) = logicalPrefix R z x m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [rawPrefix_succ, ih]
    rfl

/-- The entire logical-run image lands in the legal subtype, retaining all null seeds and impossible outcomes. -/
def logicalLegalPath (R : RawRules Z S O) (z : Z) (x : ℕ → O) : legalPaths R :=
  ⟨logicalRawPath R z x, fun m => by
    rw [logicalRawPath_prefix]
    exact logicalPrefix_consistent R z x m⟩

/-- Raw every-path caps and bounds on every point of the legal sample space are exactly equivalent. -/
theorem capped_iff_legal_all_points (P : QuditProtocol Z d n) (N : ℕ) :
    Capped P N ↔ ∀ p : legalPaths P.toRawRules, executionTime P p.val ≤ (N : WithTop ℕ) := by
  constructor
  · intro h p
    exact executionTime_le_of_capped P N h p.val
  · intro h
    change EveryPathCap P.toRawRules N
    intro z x
    have hp := (legalPath_stoppingTime_le P (logicalLegalPath P.toRawRules z x) N).mp
      (h (logicalLegalPath P.toRawRules z x))
    change rawPrefix N (logicalRawPath P.toRawRules z x) ∉ activePrefix P.toRawRules N at hp
    rw [logicalRawPath_prefix] at hp
    exact hp

end LocalCertification.Protocol
