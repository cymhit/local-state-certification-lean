import LocalCertification.Protocol.BornTrajectory
import Mathlib.MeasureTheory.Measure.Continuity

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information Topology
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- A finite history reports decision j only if the actual executor has stopped by that horizon. -/
def prefixDecisionEvent (P : QuditProtocol Z d n) (j : Fin 2) (m : ℕ) :
    Set (SlotHistory Z (CertificationGaussian.QuditIndex d n) m) :=
  {h | h ∉ activePrefix P.toRawRules m ∧ actionDecision (execPrefix P.toRawRules m h).2 = j}

theorem prefixDecisionEvent_measurable (P : QuditProtocol Z d n) (j : Fin 2) (m : ℕ) :
    MeasurableSet (prefixDecisionEvent P j m) :=
  (activePrefix_measurable P.toRawRules m).compl.inter
    ((actionDecision_measurable.comp (measurable_snd.comp (execPrefix_measurable P.toRawRules m)))
      (measurableSet_singleton j))

/-- This event is on the original seed/slot space, with the genuine first stopping time. -/
def truncatedDecisionEvent (P : QuditProtocol Z d n) (j : Fin 2) (m : ℕ) :
    Set (RawSample Z (CertificationGaussian.QuditIndex d n)) :=
  {p | executionTime P p ≤ (m : WithTop ℕ) ∧ executionDecision P p = j}

theorem truncatedDecisionEvent_measurable (P : QuditProtocol Z d n) (j : Fin 2) (m : ℕ) :
    MeasurableSet (truncatedDecisionEvent P j m) :=
  ((executionTime_measurable P) measurableSet_Iic).inter
    ((executionDecision_measurable P) (measurableSet_singleton j))

/-- Increasing truncations do not assert that the truncated protocol has the final error guarantee. -/
theorem truncatedDecisionEvent_mono (P : QuditProtocol Z d n) (j : Fin 2) :
    Monotone (truncatedDecisionEvent P j) := by
  intro m k hmk p hp
  exact ⟨hp.1.trans (Nat.cast_le.mpr hmk), hp.2⟩

/-- The finite report agrees with T≤m and the terminal decision on consistent histories only. -/
theorem prefixDecisionEvent_iff_of_consistent (P : QuditProtocol Z d n)
    (p : RawSample Z (CertificationGaussian.QuditIndex d n))
    (hc : ∀ m, ConsistentPrefix P.toRawRules m (rawPrefix m p)) (j : Fin 2) (m : ℕ) :
    rawPrefix m p ∈ prefixDecisionEvent P j m ↔ p ∈ truncatedDecisionEvent P j m := by
  have he := trajectoryPrefix_eq_logical P.toRawRules (packTrajectory p) hc m
  change logicalPrefix P.toRawRules p.1 (fun k => (p.2 k).getD default) m = rawPrefix m p at he
  have hs : runState P.toRawRules p.1 (fun k => (p.2 k).getD default) m =
      execPrefix P.toRawRules m (rawPrefix m p) := congrArg (execPrefix P.toRawRules m) he
  change (¬actionContinues (execPrefix P.toRawRules m (rawPrefix m p)).2 = true) ∧
    actionDecision (execPrefix P.toRawRules m (rawPrefix m p)).2 = j ↔ _
  rw [← hs]
  change (¬runContinues P.toRawRules p.1 (fun k => (p.2 k).getD default) m) ∧ _ ↔ _
  rw [← stoppingTime_le_iff]
  constructor
  · rintro ⟨ht,hj⟩
    refine ⟨ht, ?_⟩
    change terminalDecision P.toRawRules p.1 (fun k => (p.2 k).getD default) = j
    rw [terminalDecision_eq_of_stopped _ _ _ m ((stoppingTime_le_iff _ _ _ m).mp ht)]
    exact hj
  · rintro ⟨ht,hj⟩
    refine ⟨ht, ?_⟩
    change terminalDecision P.toRawRules p.1 (fun k => (p.2 k).getD default) = j at hj
    rw [terminalDecision_eq_of_stopped _ _ _ m ((stoppingTime_le_iff _ _ _ m).mp ht)] at hj
    exact hj

/-- Actual finite-prefix probabilities equal the actual infinite-law truncated decision probabilities. -/
theorem prefixDecisionEvent_measure (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : Fin 2) (m : ℕ) :
    executionPrefixLaw P ρ m (prefixDecisionEvent P j m) =
      executionLaw P ρ (truncatedDecisionEvent P j m) := by
  rw [← executionLaw_prefix, Measure.map_apply (rawPrefix_measurable m) (prefixDecisionEvent_measurable P j m)]
  apply measure_congr
  filter_upwards [executionLaw_ae_consistent P ρ] with p hp
  exact propext (prefixDecisionEvent_iff_of_consistent P p hp j m)

theorem iUnion_truncatedDecisionEvent (P : QuditProtocol Z d n) (j : Fin 2) :
    (⋃ m : ℕ, truncatedDecisionEvent P j m) =
      {p | executionTime P p ≠ ⊤ ∧ executionDecision P p = j} := by
  ext p
  simp only [Set.mem_iUnion, truncatedDecisionEvent, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m,ht,hj⟩
    exact ⟨ne_top_of_le_ne_top (WithTop.natCast_ne_top m) ht, hj⟩
  · rintro ⟨ht,hj⟩
    obtain ⟨m,hm⟩ := WithTop.ne_top_iff_exists.mp ht
    exact ⟨m, hm.ge, hj⟩

/-- Final decision probabilities are limits of finite reports under each input's own termination law. -/
theorem prefixDecisionEvent_probability_tendsto (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (hT : Terminates P ρ) (j : Fin 2) :
    Tendsto (fun m => (executionPrefixLaw P ρ m).real (prefixDecisionEvent P j m)) atTop
      (𝓝 ((executionLaw P ρ).real {p | executionDecision P p = j})) := by
  have hu : executionLaw P ρ (⋃ m : ℕ, truncatedDecisionEvent P j m) =
      executionLaw P ρ {p | executionDecision P p = j} := by
    rw [iUnion_truncatedDecisionEvent]
    apply measure_congr
    filter_upwards [hT] with p hp
    exact propext (and_iff_right hp)
  have ht := tendsto_measure_iUnion_atTop (μ := executionLaw P ρ) (truncatedDecisionEvent_mono P j)
  rw [hu] at ht
  have h := (ENNReal.tendsto_toReal (measure_ne_top (executionLaw P ρ) _)).comp ht
  simpa only [Function.comp_def, Measure.real, prefixDecisionEvent_measure] using h

end LocalCertification.Protocol
