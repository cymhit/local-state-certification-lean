import LocalCertification.Protocol.MeasurableExecutionRules
import LocalCertification.Information.KernelTerminalInformation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.ENNReal.ENatENNReal

/-! First stopping time, actual extended cost and terminal finite reports for
the arbitrary measurable causal executor. All identities retain infinite time. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open LocalCertification.Information.KernelHistory
open scoped ENNReal BigOperators Topology Classical
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u
variable {Z S Ω : Type u} [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]

abbrev PathActive (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) (n : ℕ) : Prop :=
  rawPrefix n p ∈ active R n

theorem pathActive_measurable (R : RawRules Z S Ω) (n : ℕ) :
    MeasurableSet {p : Sample Z (Slot Ω) | PathActive R p n} :=
  (rawPrefix_measurable n) (active_measurable R n)

theorem pathState_after_stop (R : RawRules Z S Ω) (p : Sample Z (Slot Ω))
    (n : ℕ) (j : Fin 2) (hj : state R n (rawPrefix n p) = Sum.inl j) (k : ℕ) :
    state R (n+k) (rawPrefix (n+k) p) = Sum.inl j := by
  induction k with
  | zero => simpa using hj
  | succ k ih => exact state_absorbing R _ j ih (p.2 (n+k))

theorem pathActive_antitone (R : RawRules Z S Ω) (p : Sample Z (Slot Ω))
    {m n : ℕ} (hmn : m ≤ n) (hn : PathActive R p n) : PathActive R p m := by
  by_contra hm
  obtain ⟨j, hj⟩ : ∃ j, state R m (rawPrefix m p) = Sum.inl j := by
    cases he : state R m (rawPrefix m p) with
    | inl j => exact ⟨j, rfl⟩
    | inr v => exact False.elim (hm ⟨v, he⟩)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨v, hv⟩ := hn
  rw [pathState_after_stop R p m j hj k] at hv
  cases hv

def stoppingTime (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) : ℕ∞ := by
  classical
  exact if h : ∃ n, ¬PathActive R p n then (Nat.find h : ℕ∞) else ⊤

def terminalDecision (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) : Fin 2 := by
  classical
  exact if h : ∃ n, ¬PathActive R p n then decision (state R (Nat.find h) (rawPrefix (Nat.find h) p)) else 0

theorem stoppingTime_le_iff (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) (m : ℕ) :
    stoppingTime R p ≤ (m : ℕ∞) ↔ ¬PathActive R p m := by
  classical
  by_cases h : ∃ n, ¬PathActive R p n
  · simp only [stoppingTime, dite_eq_left h, Nat.cast_le]
    exact ⟨fun hle ha => Nat.find_spec h (pathActive_antitone R p hle ha), fun hm => Nat.find_min' h hm⟩
  · simp only [stoppingTime, dite_eq_right h]
    exact iff_of_false (not_le_of_gt (WithTop.natCast_lt_top m)) (not_exists.mp h m)

theorem stoppingTime_eq_top_iff (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) :
    stoppingTime R p = ⊤ ↔ ∀ n, PathActive R p n := by
  classical
  by_cases h : ∃ n, ¬PathActive R p n
  · simp only [stoppingTime, dite_eq_left h, ENat.natCast_ne_top, false_iff]
    exact fun ha => Nat.find_spec h (ha (Nat.find h))
  · simp only [stoppingTime, dite_eq_right h, true_iff]
    exact fun n => not_not.mp (not_exists.mp h n)

theorem terminalDecision_of_stopped (R : RawRules Z S Ω) (p : Sample Z (Slot Ω))
    (m : ℕ) (hm : stoppingTime R p ≤ (m : ℕ∞)) :
    terminalDecision R p = decision (state R m (rawPrefix m p)) := by
  classical
  have h : ∃ n, ¬PathActive R p n := ⟨m, (stoppingTime_le_iff R p m).mp hm⟩
  obtain ⟨j, hj⟩ : ∃ j, state R (Nat.find h) (rawPrefix (Nat.find h) p) = Sum.inl j := by
    cases he : state R (Nat.find h) (rawPrefix (Nat.find h) p) with
    | inl j => exact ⟨j, rfl⟩
    | inr v => exact False.elim (Nat.find_spec h ⟨v, he⟩)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.find_min' h ((stoppingTime_le_iff R p m).mp hm))
  simp only [terminalDecision, dite_eq_left h]
  rw [hj, hk, pathState_after_stop R p (Nat.find h) j hj k]
  rfl

theorem terminalDecision_of_top (R : RawRules Z S Ω) (p : Sample Z (Slot Ω))
    (ht : stoppingTime R p = ⊤) : terminalDecision R p = 0 := by
  classical
  have h : ¬∃ n, ¬PathActive R p n := by
    rintro ⟨n, hn⟩
    exact hn ((stoppingTime_eq_top_iff R p).mp ht n)
  simp only [terminalDecision, dite_eq_right h]

theorem stoppingTime_measurable (R : RawRules Z S Ω) : Measurable (stoppingTime R) := by
  have hm (m : ℕ) : MeasurableSet {p : Sample Z (Slot Ω) | stoppingTime R p ≤ (m : ℕ∞)} := by
    simp only [stoppingTime_le_iff]
    exact (pathActive_measurable R m).compl
  apply measurable_to_countable'
  intro t
  change MeasurableSet {p : Sample Z (Slot Ω) | stoppingTime R p = t}
  cases t with
  | top =>
    simp only [stoppingTime_eq_top_iff]
    convert MeasurableSet.iInter (pathActive_measurable R) using 1
    ext p
    simp
  | coe n =>
    cases n with
    | zero => simpa only [Nat.cast_zero, nonpos_iff_eq_zero] using hm 0
    | succ n =>
      have he : {p : Sample Z (Slot Ω) | stoppingTime R p = ((n+1 : ℕ) : ℕ∞)} =
          {p | stoppingTime R p ≤ ((n+1 : ℕ) : ℕ∞)} \ {p | stoppingTime R p ≤ (n : ℕ∞)} := by
        ext p
        simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
        cases ht : stoppingTime R p with
        | top =>
          simp
          simpa only [Nat.cast_add, Nat.cast_one] using (ENat.natCast_ne_top (n+1)).symm
        | coe k =>
          simp only [ENat.natCast_inj, ENat.natCast_le_natCast]
          omega
      rw [he]
      exact (hm (n+1)).diff (hm n)

theorem terminalDecision_measurable (R : RawRules Z S Ω) : Measurable (terminalDecision R) := by
  apply measurable_to_countable'
  intro j
  have he : {p : Sample Z (Slot Ω) | terminalDecision R p = j} =
      {p | stoppingTime R p = ⊤ ∧ j = 0} ∪
      ⋃ m : ℕ, {p | stoppingTime R p ≤ (m : ℕ∞) ∧ decision (state R m (rawPrefix m p)) = j} := by
    ext p
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    constructor
    · intro hj
      by_cases ht : stoppingTime R p = ⊤
      · exact Or.inl ⟨ht, hj.symm.trans (terminalDecision_of_top R p ht)⟩
      · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ht
        exact Or.inr ⟨m, hm.ge, (terminalDecision_of_stopped R p m hm.ge).symm.trans hj⟩
    · rintro (⟨ht, rfl⟩ | ⟨m, hm, hj⟩)
      · exact terminalDecision_of_top R p ht
      · exact (terminalDecision_of_stopped R p m hm).trans hj
  change MeasurableSet {p | terminalDecision R p = j}
  rw [he]
  apply MeasurableSet.union
  · exact ((stoppingTime_measurable R) (measurableSet_singleton ⊤)).inter
      (by by_cases hj : j = 0 <;> simp only [hj] <;> exact MeasurableSet.const _)
  · exact MeasurableSet.iUnion (fun m => ((stoppingTime_measurable R)
      (Set.to_countable (Set.Iic (m : ℕ∞))).measurableSet).inter
      ((decision_measurable m).comp ((state_measurable R m).comp (rawPrefix_measurable m))
        (measurableSet_singleton j)))

def copyCount (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) : ℕ → ℕ
  | 0 => 0
  | n+1 => copyCount R p n + if PathActive R p n then 1 else 0

theorem copyCount_eq_min (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) (m : ℕ) :
    (copyCount R p m : ℕ∞) = min (stoppingTime R p) (m : ℕ∞) := by
  classical
  by_cases h : ∃ n, ¬PathActive R p n
  · have hc : ∀ m, copyCount R p m = min (Nat.find h) m := by
      intro m
      induction m with
      | zero => simp [copyCount]
      | succ m ih =>
        by_cases hm : m < Nat.find h
        · rw [copyCount, ih, ite_eq_left (not_not.mp (Nat.find_min h hm))]
          omega
        · have hn : ¬PathActive R p m := fun ha =>
            Nat.find_spec h (pathActive_antitone R p (Nat.le_of_not_gt hm) ha)
          rw [copyCount, ih, ite_eq_right hn]
          omega
    rw [hc]
    simp only [stoppingTime, dite_eq_left h]
    norm_cast
  · have ha : ∀ n, PathActive R p n := fun n => not_not.mp (not_exists.mp h n)
    have hc : ∀ m, copyCount R p m = m := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => simp only [copyCount, ih, ite_eq_left (ha m)]
    rw [hc]
    simp only [stoppingTime, dite_eq_right h, min_eq_right le_top]

def cost (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) : ℝ≥0∞ := ENat.toENNReal (stoppingTime R p)

theorem cost_measurable (R : RawRules Z S Ω) : Measurable (cost R) :=
  (measurable_of_countable ENat.toENNReal).comp (stoppingTime_measurable R)

theorem copyCount_ennreal_min (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) (m : ℕ) :
    (copyCount R p m : ℝ≥0∞) = min (cost R p) (m : ℝ≥0∞) := by
  have h := (congrArg ENat.toENNReal (copyCount_eq_min R p m)).trans
    (ENat.toENNReal_min (stoppingTime R p) (m : ℕ∞))
  simpa only [ENat.toENNReal_coe, cost] using h

def requestCount (R : RawRules Z S Ω) : ∀ m, History Z Ω m → ℝ≥0∞
  | 0 => fun _ => 0
  | m+1 => fun h => requestCount R m h.1 + (active R m).indicator (fun _ => 1) h.1

theorem requestCount_measurable (R : RawRules Z S Ω) (m : ℕ) : Measurable (requestCount R m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    exact (ih.comp measurable_fst).add
      ((measurable_const.indicator (active_measurable R m)).comp measurable_fst)

theorem requestCount_rawPrefix (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) (m : ℕ) :
    requestCount R m (rawPrefix m p) = (copyCount R p m : ℝ≥0∞) := by
  induction m with
  | zero => simp [requestCount, copyCount]
  | succ m ih =>
    change requestCount R m (rawPrefix m p) + (active R m).indicator (fun _ => 1) (rawPrefix m p) = _
    rw [ih, copyCount, Nat.cast_add]
    congr 1
    by_cases hm : PathActive R p m
    · rw [Set.indicator_of_mem hm, ite_eq_left hm]; norm_num
    · rw [Set.indicator_of_notMem hm, ite_eq_right hm]; norm_num

theorem requestCount_lintegral (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (History Z Ω n) (Slot Ω)) [∀ n, IsMarkovKernel (κ n)] (m : ℕ) :
    (∫⁻ h, requestCount R m h ∂prefixLaw seed κ m) =
      ∑ i ∈ Finset.range m, prefixLaw seed κ i (active R i) := by
  induction m with
  | zero =>
    change (∫⁻ h : Z, (0 : ℝ≥0∞) ∂seed) = ∑ i ∈ Finset.range 0, _
    simp
  | succ m ih =>
    change (∫⁻ h, requestCount R m h.1 + (active R m).indicator (fun _ => 1) h.1
      ∂(prefixLaw seed κ m ⊗ₘ κ m)) = _
    have hm : Measurable (fun h : History Z Ω m × Slot Ω =>
        requestCount R m h.1 + (active R m).indicator (fun _ => (1 : ℝ≥0∞)) h.1) :=
      ((requestCount_measurable R m).comp measurable_fst).add
        ((measurable_const.indicator (active_measurable R m)).comp measurable_fst)
    rw [Measure.lintegral_compProd hm]
    simp only [lintegral_const, measure_univ, mul_one]
    rw [lintegral_add_left (requestCount_measurable R m), ih,
      lintegral_indicator_const (active_measurable R m), one_mul, Finset.sum_range_succ]

/-- Exact requested-copy count for the actual input law, including immediate
stopping and infinite time. No finite-expectation assumption is used. -/
theorem expected_min (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] (m : ℕ) :
    (∑ i ∈ Finset.range m, prefixLaw seed (stoppedKernel R K) i (active R i)) =
      ∫⁻ p, min (cost R p) (m : ℝ≥0∞) ∂stoppedLaw R seed K := by
  rw [← requestCount_lintegral R seed (stoppedKernel R K) m, ← stoppedLaw_prefix R seed K m,
    lintegral_map (requestCount_measurable R m) (rawPrefix_measurable m)]
  apply lintegral_congr
  intro p
  rw [requestCount_rawPrefix, copyCount_ennreal_min]

theorem expected_truncations (R : RawRules Z S Ω) (μ : Measure (Sample Z (Slot Ω))) :
    (⨆ m : ℕ, ∫⁻ p, min (cost R p) (m : ℝ≥0∞) ∂μ) = ∫⁻ p, cost R p ∂μ :=
  LocalCertification.Information.KernelTerminal.expected_truncations μ (cost R) (cost_measurable R)

def prefixDecisionEvent (R : RawRules Z S Ω) (j : Fin 2) (m : ℕ) : Set (History Z Ω m) :=
  {h | h ∉ active R m ∧ decision (state R m h) = j}

theorem prefixDecisionEvent_measurable (R : RawRules Z S Ω) (j : Fin 2) (m : ℕ) :
    MeasurableSet (prefixDecisionEvent R j m) :=
  (active_measurable R m).compl.inter
    (((decision_measurable m).comp (state_measurable R m)) (measurableSet_singleton j))

theorem prefixDecisionEvent_iff (R : RawRules Z S Ω) (p : Sample Z (Slot Ω)) (j : Fin 2) (m : ℕ) :
    rawPrefix m p ∈ prefixDecisionEvent R j m ↔
      p ∈ LocalCertification.Information.KernelTerminal.truncatedDecisionEvent
        (stoppingTime R) (terminalDecision R) j m := by
  change (¬PathActive R p m ∧ decision (state R m (rawPrefix m p)) = j) ↔
    (stoppingTime R p ≤ (m : ℕ∞) ∧ terminalDecision R p = j)
  rw [← stoppingTime_le_iff]
  constructor
  · rintro ⟨ht, hj⟩
    exact ⟨ht, (terminalDecision_of_stopped R p m ht).trans hj⟩
  · rintro ⟨ht, hj⟩
    exact ⟨ht, (terminalDecision_of_stopped R p m ht).symm.trans hj⟩

/-- This identity is pointwise before taking probabilities, hence applies to
each input's own Born law without completing or shrinking any path space. -/
theorem prefixDecisionEvent_measure (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] (j : Fin 2) (m : ℕ) :
    prefixLaw seed (stoppedKernel R K) m (prefixDecisionEvent R j m) =
      stoppedLaw R seed K (LocalCertification.Information.KernelTerminal.truncatedDecisionEvent
        (stoppingTime R) (terminalDecision R) j m) := by
  rw [← stoppedLaw_prefix R seed K m,
    Measure.map_apply (rawPrefix_measurable m) (prefixDecisionEvent_measurable R j m)]
  congr 1
  ext p
  exact prefixDecisionEvent_iff R p j m

/-- Complete actual execution and exact stopped-cost contract. The kernel is
constructed from the supplied measurable setting law, not a field assumption. -/
theorem exists_stopped_execution (R : RawRules Z S Ω) (seed : Measure Z) [IsProbabilityMeasure seed]
    (K : Kernel S Ω) [IsMarkovKernel K] :
    ∃ (κ : ∀ n, Kernel (History Z Ω n) (Slot Ω)) (hκ : ∀ n, IsMarkovKernel (κ n)),
      letI := hκ
      ∃ (T : Sample Z (Slot Ω) → ℕ∞) (D : Sample Z (Slot Ω) → Fin 2),
        Measurable T ∧ Measurable D ∧
        (∀ n h, κ n h = match state R n h with
          | Sum.inl _ => Measure.dirac (Sum.inl ())
          | Sum.inr (_, s) => (K s).map Sum.inr) ∧
        (∀ p (m : ℕ), T p ≤ (m : ℕ∞) ↔ rawPrefix m p ∉ active R m) ∧
        (∀ p (m : ℕ), T p ≤ (m : ℕ∞) → D p = decision (state R m (rawPrefix m p))) ∧
        (∀ p, T p = ⊤ → D p = 0) ∧
        (∀ m, (∑ i ∈ Finset.range m, prefixLaw seed κ i (active R i)) =
          ∫⁻ p, min (ENat.toENNReal (T p)) (m : ℝ≥0∞) ∂executionLaw seed κ) := by
  refine ⟨stoppedKernel R K, fun _ => inferInstance, stoppingTime R, terminalDecision R,
    stoppingTime_measurable R, terminalDecision_measurable R, stoppedKernel_apply R K,
    stoppingTime_le_iff R, terminalDecision_of_stopped R, terminalDecision_of_top R, ?_⟩
  intro m
  exact expected_min R seed K m

end LocalCertification.Protocol.MeasurableExecution
