import LocalCertification.Protocol.SeedTransport

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Preorder LocalCertification.Information
open scoped LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v
variable {Z : Type u} {O : Type v} [MeasurableSpace Z] [Fintype O]

/-- The i-th primitive slot of a finite recursive history. -/
def historySlot : (m : ℕ) → SlotHistory Z O m → Fin m → Option O
  | 0, _, i => Fin.elim0 i
  | m+1, h, i => Fin.lastCases h.2 (fun j => historySlot m h.1 j) i

theorem historySlot_measurable (m : ℕ) (i : Fin m) : Measurable (fun h : SlotHistory Z O m => historySlot m h i) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    change Measurable (fun h : SlotHistory Z O m × Option O => Fin.lastCases (motive := fun _ : Fin (m+1) => Option O) h.2 (fun j => historySlot m h.1 j) i)
    cases i using Fin.lastCases with
    | last => simpa only [historySlot, Fin.lastCases_last] using
        (measurable_snd : Measurable (fun h : SlotHistory Z O m × Option O => h.2))
    | cast i => simpa only [historySlot, Fin.lastCases_castSucc, Function.comp_def] using (ih i).comp measurable_fst

omit [MeasurableSpace Z] [Fintype O] in
theorem slotSeed_rawPrefix (m : ℕ) (p : RawSample Z O) : slotSeed m (rawPrefix m p) = p.1 := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih

omit [MeasurableSpace Z] [Fintype O] in
theorem historySlot_rawPrefix (m : ℕ) (p : RawSample Z O) (i : Fin m) :
    historySlot m (rawPrefix m p) i = p.2 i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases i using Fin.lastCases with
    | last => simp [historySlot, rawPrefix_succ]
    | cast i => simpa only [historySlot, rawPrefix_succ, Fin.lastCases_castSucc, Fin.val_castSucc] using ih i

/-- Recover all heterogeneous trajectory coordinates from the complete finite seed/slot prefix. -/
def encodeTrajectoryPrefix (m : ℕ) (h : SlotHistory Z O m) : (i : Finset.Iic m) → TrajectoryCoord Z O i
  | ⟨0,_⟩ => ULift.up (slotSeed m h)
  | ⟨k+1,hk⟩ => ULift.up (historySlot m h ⟨k,Nat.lt_of_succ_le (Finset.mem_Iic.mp hk)⟩)

theorem encodeTrajectoryPrefix_measurable (m : ℕ) : Measurable (encodeTrajectoryPrefix (Z := Z) (O := O) m) := by
  apply measurable_pi_iff.mpr
  rintro ⟨k,hk⟩
  cases k with
  | zero => exact measurable_up.comp (slotSeed_measurable m)
  | succ k => exact measurable_up.comp (historySlot_measurable m ⟨k,Nat.lt_of_succ_le (Finset.mem_Iic.mp hk)⟩)

omit [MeasurableSpace Z] [Fintype O] in
theorem encodeTrajectoryPrefix_rawPrefix (m : ℕ) (p : RawSample Z O) :
    encodeTrajectoryPrefix m (rawPrefix m p) = frestrictLe m (packTrajectory p) := by
  funext i
  rcases i with ⟨k,hk⟩
  cases k with
  | zero => exact congrArg ULift.up (slotSeed_rawPrefix m p)
  | succ k => exact congrArg ULift.up (historySlot_rawPrefix m p ⟨k,Nat.lt_of_succ_le (Finset.mem_Iic.mp hk)⟩)

/-- Probability laws on the original arbitrary seed and infinite finite-slot stream are determined by all finite prefixes.
This uses generating measurable cylinders, with no standard-Borel condition on the seed. -/
theorem rawLaw_ext_prefix (μ ν : Measure (RawSample Z O)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ m : ℕ, μ.map (rawPrefix m) = ν.map (rawPrefix m)) : μ = ν := by
  have hm : ∀ m : ℕ, (μ.map packTrajectory).map (frestrictLe m) =
      (ν.map packTrajectory).map (frestrictLe m) := by
    intro m
    have hc (ξ : Measure (RawSample Z O)) :
        (ξ.map packTrajectory).map (frestrictLe m) = (ξ.map (rawPrefix m)).map (encodeTrajectoryPrefix m) := by
      rw [Measure.map_map (measurable_frestrictLe m) packTrajectory_measurable,
        Measure.map_map (encodeTrajectoryPrefix_measurable m) (rawPrefix_measurable m)]
      apply congrArg (Measure.map · ξ)
      funext p
      exact (encodeTrajectoryPrefix_rawPrefix m p).symm
    rw [hc μ, hc ν, h m]
  have hprob (ξ : Measure (RawSample Z O)) [IsProbabilityMeasure ξ] : IsProbabilityMeasure (ξ.map packTrajectory) := by
    constructor
    rw [Measure.map_apply packTrajectory_measurable MeasurableSet.univ]
    simp
  let := hprob μ
  let := hprob ν
  have he : μ.map packTrajectory = ν.map packTrajectory := by
    apply ext_of_generate_finite (measurableCylinders (TrajectoryCoord Z O))
      generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    · intro s hs
      rw [measurableCylinders_nat] at hs
      obtain ⟨m,hs⟩ := Set.mem_iUnion.mp hs
      obtain ⟨S,hs⟩ := Set.mem_iUnion.mp hs
      obtain ⟨hS,hs⟩ := Set.mem_iUnion.mp hs
      have heq : s = cylinder (Finset.Iic m) S := Set.mem_singleton_iff.mp hs
      subst s
      have hp := congrArg (fun ξ => ξ S) (hm m)
      rw [Measure.map_apply (measurable_frestrictLe m) hS, Measure.map_apply (measurable_frestrictLe m) hS] at hp
      exact hp
    · simp only [measure_univ]
  exact MeasurableEquiv.map_measurableEquiv_injective (rawTrajectoryEquiv (Z := Z) (O := O)).symm he

end LocalCertification.Protocol
