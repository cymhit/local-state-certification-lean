import LocalCertification.Protocol.Trajectory
import LocalCertification.Protocol.LogicalMeasurability

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- The seed and slots of the real trajectory, without any quotient by null events. -/
def trajectorySeed (ω : Π t, TrajectoryCoord Z O t) : Z := (ω 0).down

def trajectorySlot (ω : Π t, TrajectoryCoord Z O t) (m : ℕ) : Option O := (ω (m+1)).down

/-- Complete the stopped tail by an arbitrary fixed outcome; the completion is never measured. -/
def trajectoryOutcome (ω : Π t, TrajectoryCoord Z O t) (m : ℕ) : O := (trajectorySlot ω m).getD default

omit [MeasurableSpace O] [Inhabited O] [MeasurableSingletonClass O] in
theorem trajectorySeed_measurable : Measurable (trajectorySeed (Z := Z) (O := O)) :=
  measurable_down.comp (measurable_pi_apply 0)

omit [MeasurableSingletonClass O] in
theorem trajectoryOutcome_measurable : Measurable (trajectoryOutcome (Z := Z) (O := O)) :=
  measurable_pi_iff.mpr (fun m => (measurable_of_countable (fun o : Option O => o.getD default)).comp
    (measurable_down.comp (measurable_pi_apply (m+1))))

omit [Fintype O] [MeasurableSingletonClass O] in
/-- All consistent prefixes of a single trajectory reconstruct one and the same full logical run. -/
theorem trajectoryPrefix_eq_logical (R : RawRules Z S O) (ω : Π t, TrajectoryCoord Z O t)
    (hc : ∀ m, ConsistentPrefix R m (trajectoryPrefix m ω)) (m : ℕ) :
    logicalPrefix R (trajectorySeed ω) (trajectoryOutcome ω) m = trajectoryPrefix m ω := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (logicalPrefix R (trajectorySeed ω) (trajectoryOutcome ω) m,
      if actionContinues (execPrefix R m (logicalPrefix R (trajectorySeed ω) (trajectoryOutcome ω) m)).2 = true
        then some (trajectoryOutcome ω m) else none) = _
    rw [ih, trajectoryPrefix_succ]
    apply congrArg (fun o : Option O => (trajectoryPrefix m ω,o))
    have hs : trajectorySlot ω m ≠ none ↔ trajectoryPrefix m ω ∈ activePrefix R m := (hc (m+1)).2
    by_cases ha : trajectoryPrefix m ω ∈ activePrefix R m
    · have ha' : actionContinues (execPrefix R m (trajectoryPrefix m ω)).2 = true := ha
      rw [ite_eq_left ha']
      have hn := hs.mpr ha
      cases ho : trajectorySlot ω m with
      | none => exact False.elim (hn ho)
      | some x =>
        change some ((trajectorySlot ω m).getD default) = trajectorySlot ω m
        rw [ho]
        rfl
    · have ha' : ¬actionContinues (execPrefix R m (trajectoryPrefix m ω)).2 = true := ha
      rw [ite_eq_right ha']
      exact (not_not.mp (fun hn => ha (hs.mp hn))).symm

/-- Actual stopped trajectories satisfy every finite consistency condition simultaneously with probability one. -/
theorem stoppedTrajectory_ae_consistent (R : RawRules Z S O) (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) O) [∀ m, IsMarkovKernel (κ m)] :
    ∀ᵐ ω ∂trajectoryLaw ν (fun m => stopContinue (activePrefix R m) (activePrefix_measurable R m) (κ m)),
      ∀ m, ConsistentPrefix R m (trajectoryPrefix m ω) := by
  rw [ae_all_iff]
  intro m
  have h := prefixLaw_ae_consistent R ν κ m
  rw [← trajectoryLaw_prefix] at h
  exact (ae_map_iff (trajectoryPrefix_measurable m).aemeasurable (consistentPrefix_measurable R m)).mp h

/-- The trajectory stopping time is the genuine first stopping time of its reconstructed logical run. -/
def trajectoryStoppingTime (R : RawRules Z S O) (ω : Π t, TrajectoryCoord Z O t) : WithTop ℕ :=
  stoppingTime R (trajectorySeed ω) (trajectoryOutcome ω)

theorem trajectoryStoppingTime_measurable (R : RawRules Z S O) : Measurable (trajectoryStoppingTime R) :=
  (stoppingTime_measurable R).comp (trajectorySeed_measurable.prodMk trajectoryOutcome_measurable)

def trajectoryTerminalDecision (R : RawRules Z S O) (ω : Π t, TrajectoryCoord Z O t) : Fin 2 :=
  terminalDecision R (trajectorySeed ω) (trajectoryOutcome ω)

theorem trajectoryTerminalDecision_measurable (R : RawRules Z S O) : Measurable (trajectoryTerminalDecision R) :=
  (terminalDecision_measurable R).comp (trajectorySeed_measurable.prodMk trajectoryOutcome_measurable)

/-- The actual source-world expected active count equals E(T∧m), including infinite stopping times. -/
theorem stoppedTrajectory_expected_min (R : RawRules Z S O) (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) O) [∀ m, IsMarkovKernel (κ m)] (m : ℕ) :
    (∫⁻ h, prefixActiveCount (activePrefix R) m h
      ∂prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) m) =
    ∫⁻ ω, min (ENat.toENNReal (trajectoryStoppingTime R ω)) (m : ℝ≥0∞)
      ∂trajectoryLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) := by
  rw [← trajectoryLaw_prefix]
  rw [lintegral_map (prefixActiveCount_measurable (activePrefix R) (activePrefix_measurable R) m)
    (trajectoryPrefix_measurable m)]
  apply lintegral_congr_ae
  filter_upwards [stoppedTrajectory_ae_consistent R ν κ] with ω hω
  rw [← trajectoryPrefix_eq_logical R ω hω m, runCopyCount_eq_prefixActiveCount, runCopyCount_ennreal_min]
  rfl

/-- The full singular finite-prefix KL now has the actual stopping-time cost in the source world. -/
theorem stoppedTrajectory_klDiv_le (R : RawRules Z S O) (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) O)
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)] (L : ℝ≥0∞)
    (hL : ∀ m h, h ∈ activePrefix R m → klDiv (κ m h) (η m h) ≤ L) (m : ℕ) :
    klDiv (prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) m)
      (prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (η t)) m) ≤
      L * ∫⁻ ω, min (ENat.toENNReal (trajectoryStoppingTime R ω)) (m : ℝ≥0∞)
        ∂trajectoryLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) := by
  rw [← stoppedTrajectory_expected_min]
  exact prefixLaw_stopped_klDiv_le ν (activePrefix R) (activePrefix_measurable R) κ η L hL m

end LocalCertification.Protocol
