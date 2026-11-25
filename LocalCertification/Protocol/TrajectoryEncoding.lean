import LocalCertification.Protocol.Trajectory

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Function LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v
variable {Z : Type u} {O : Type v} [MeasurableSpace Z] [Fintype O]

/-- The literal execution sample space: original seed and a countable sequence of finite padded outcomes. -/
abbrev RawSample (Z : Type u) (O : Type v) := Z × (ℕ → Option O)

/-- Pure universe alignment, with no deletion or alteration of any seed or slot. -/
def packTrajectory (p : RawSample Z O) : (t : ℕ) → TrajectoryCoord Z O t
  | 0 => ULift.up p.1
  | m+1 => ULift.up (p.2 m)

def unpackTrajectory (ω : Π t, TrajectoryCoord Z O t) : RawSample Z O :=
  ((ω 0).down, fun m => (ω (m+1)).down)

theorem packTrajectory_measurable : Measurable (packTrajectory (Z := Z) (O := O)) := by
  apply measurable_pi_iff.mpr
  intro t
  cases t with
  | zero => exact measurable_up.comp measurable_fst
  | succ m => exact measurable_up.comp ((measurable_pi_apply m).comp measurable_snd)

theorem unpackTrajectory_measurable : Measurable (unpackTrajectory (Z := Z) (O := O)) :=
  (measurable_down.comp (measurable_pi_apply 0)).prodMk (measurable_pi_iff.mpr
    (fun m => measurable_down.comp (measurable_pi_apply (m+1))))

omit [MeasurableSpace Z] [Fintype O] in
theorem pack_unpack_trajectory (ω : Π t, TrajectoryCoord Z O t) : packTrajectory (unpackTrajectory ω) = ω := by
  funext t
  cases t <;> rfl

omit [MeasurableSpace Z] [Fintype O] in
theorem unpack_pack_trajectory (p : RawSample Z O) : unpackTrajectory (packTrajectory p) = p := rfl

/-- This is a global measurable equivalence of primitive carriers, distinct from public-record decoding. -/
def rawTrajectoryEquiv : (Π t, TrajectoryCoord Z O t) ≃ᵐ RawSample Z O where
  toFun := unpackTrajectory
  invFun := packTrajectory
  left_inv := pack_unpack_trajectory
  right_inv := unpack_pack_trajectory
  measurable_toFun := unpackTrajectory_measurable
  measurable_invFun := packTrajectory_measurable

def rawPrefix (m : ℕ) (p : RawSample Z O) : SlotHistory Z O m := trajectoryPrefix m (packTrajectory p)

theorem rawPrefix_measurable (m : ℕ) : Measurable (rawPrefix (Z := Z) (O := O) m) :=
  (trajectoryPrefix_measurable m).comp packTrajectory_measurable

omit [MeasurableSpace Z] [Fintype O] in
theorem rawPrefix_zero (p : RawSample Z O) : rawPrefix 0 p = ULift.up p.1 := rfl

omit [MeasurableSpace Z] [Fintype O] in
theorem rawPrefix_succ (m : ℕ) (p : RawSample Z O) : rawPrefix (m+1) p = (rawPrefix m p,p.2 m) := rfl

/-- Actual infinite execution law on the literal original seed/slot sample space. -/
def rawTrajectoryLaw (ν : Measure Z) (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] : Measure (RawSample Z O) :=
  (trajectoryLaw ν κ).map unpackTrajectory

instance rawTrajectoryLaw_probability (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) [∀ m, IsMarkovKernel (κ m)] :
    IsProbabilityMeasure (rawTrajectoryLaw ν κ) := by
  constructor
  rw [rawTrajectoryLaw, Measure.map_apply unpackTrajectory_measurable MeasurableSet.univ]
  simp

/-- Every finite raw prefix has exactly its actual iterated law. -/
theorem rawTrajectoryLaw_prefix (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) [∀ m, IsMarkovKernel (κ m)] (m : ℕ) :
    (rawTrajectoryLaw ν κ).map (rawPrefix m) = prefixLaw ν κ m := by
  rw [rawTrajectoryLaw, Measure.map_map (rawPrefix_measurable m) unpackTrajectory_measurable]
  have he : rawPrefix (Z := Z) (O := O) m ∘ unpackTrajectory = trajectoryPrefix m := by
    funext ω
    exact congrArg (trajectoryPrefix m) (pack_unpack_trajectory ω)
  rw [he, trajectoryLaw_prefix]

end LocalCertification.Protocol
