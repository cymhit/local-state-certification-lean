import LocalCertification.Protocol.TrajectoryExecution

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- Copy cost is an extended nonnegative real; nontermination has cost infinity. -/
def trajectoryCost (R : RawRules Z S O) (ω : Π t, TrajectoryCoord Z O t) : ℝ≥0∞ :=
  ENat.toENNReal (trajectoryStoppingTime R ω)

theorem trajectoryCost_measurable (R : RawRules Z S O) : Measurable (trajectoryCost R) :=
  (measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t)).comp
    (trajectoryStoppingTime_measurable R)

/-- Natural truncations increase to every extended nonnegative real, including infinity. -/
theorem ennreal_iSup_min_nat (x : ℝ≥0∞) : (⨆ m : ℕ, min x (m : ℝ≥0∞)) = x := by
  rcases eq_top_or_lt_top x with rfl | hx
  · simpa only [min_eq_right le_top] using ENNReal.iSup_natCast
  · obtain ⟨m,hm⟩ := ENNReal.exists_nat_gt (ne_of_lt hx)
    apply le_antisymm (iSup_le (fun _ => min_le_left _ _))
    exact le_iSup_of_le m (by rw [min_eq_left (le_of_lt hm)])

/-- Monotone convergence of actual truncated stopping costs, with no finite-expectation assumption. -/
theorem trajectory_expected_truncations (R : RawRules Z S O)
    (μ : Measure (Π t, TrajectoryCoord Z O t)) :
    (⨆ m : ℕ, ∫⁻ ω, min (trajectoryCost R ω) (m : ℝ≥0∞) ∂μ) = ∫⁻ ω, trajectoryCost R ω ∂μ := by
  rw [← lintegral_iSup (fun m => (trajectoryCost_measurable R).min measurable_const)
    (fun a b hab ω => min_le_min_left _ (Nat.cast_le.mpr hab))]
  simp_rw [ennreal_iSup_min_nat]

/-- A uniform finite-horizon KL bound by the true expected stopping time in the source world.
All quantities remain extended: L=0 and infinite cost are not replaced by informal arithmetic. -/
theorem stoppedTrajectory_klDiv_le_expected (R : RawRules Z S O) (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) O)
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)] (L : ℝ≥0∞)
    (hL : ∀ m h, h ∈ activePrefix R m → klDiv (κ m h) (η m h) ≤ L) (m : ℕ) :
    klDiv (prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) m)
      (prefixLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (η t)) m) ≤
      L * ∫⁻ ω, trajectoryCost R ω
        ∂trajectoryLaw ν (fun t => stopContinue (activePrefix R t) (activePrefix_measurable R t) (κ t)) := by
  refine (stoppedTrajectory_klDiv_le R ν κ η L hL m).trans ?_
  gcongr with ω
  exact min_le_left _ _

end LocalCertification.Protocol
