import LocalCertification.Protocol.FullRecord
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Function Finset Preorder LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v

/-- One arbitrary measurable seed coordinate followed by finite outcome slots, aligned only by ULift. -/
abbrev TrajectoryCoord (Z : Type u) (O : Type v) : ℕ → Type (max u v)
  | 0 => ULift.{v} Z
  | _+1 => ULift.{u} (Option O)

variable {Z : Type u} {O : Type v} [MeasurableSpace Z] [Fintype O]

@[reducible] instance trajectoryCoordMeasurable : (m : ℕ) → MeasurableSpace (TrajectoryCoord Z O m)
  | 0 => inferInstanceAs (MeasurableSpace (ULift.{v} Z))
  | _+1 => inferInstanceAs (MeasurableSpace (ULift.{u} (Option O)))

/-- Deterministic coordinate decoding into the already established recursive primitive histories. -/
def decodeTrajectoryPrefix : (m : ℕ) → (Π i : Iic m, TrajectoryCoord Z O i) → SlotHistory Z O m
  | 0 => fun f => f ⟨0, by simp⟩
  | m+1 => fun f =>
      (decodeTrajectoryPrefix m (frestrictLe₂ (Nat.le_succ m) f), (f ⟨m+1,by simp⟩).down)

theorem decodeTrajectoryPrefix_measurable (m : ℕ) :
    Measurable (decodeTrajectoryPrefix (Z := Z) (O := O) m) := by
  induction m with
  | zero => exact measurable_pi_apply (⟨0,by simp⟩ : Iic (0:ℕ))
  | succ m ih =>
    exact (ih.comp (measurable_frestrictLe₂ _)).prodMk
      (measurable_down.comp (measurable_pi_apply (⟨m+1,by simp⟩ : Iic (m+1))))

def trajectoryPrefix (m : ℕ) (ω : Π t, TrajectoryCoord Z O t) : SlotHistory Z O m :=
  decodeTrajectoryPrefix m (frestrictLe m ω)

theorem trajectoryPrefix_measurable (m : ℕ) : Measurable (trajectoryPrefix (Z := Z) (O := O) m) :=
  (decodeTrajectoryPrefix_measurable m).comp (measurable_frestrictLe m)

omit [MeasurableSpace Z] [Fintype O] in
theorem trajectoryPrefix_succ (m : ℕ) (ω : Π t, TrajectoryCoord Z O t) :
    trajectoryPrefix (m+1) ω = (trajectoryPrefix m ω, (ω (m+1)).down) := rfl

/-- Only the actual previously decoded prefix is fed to the original finite-slot kernel. -/
def trajectoryCoordKernel (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) (m : ℕ) :
    Kernel (Π i : Iic m, TrajectoryCoord Z O i) (TrajectoryCoord Z O (m+1)) :=
  ((κ m).comap (decodeTrajectoryPrefix m) (decodeTrajectoryPrefix_measurable m)).map ULift.up

instance trajectoryCoordKernel_markov
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) [∀ m, IsMarkovKernel (κ m)] (m : ℕ) :
    IsMarkovKernel (trajectoryCoordKernel κ m) := by
  unfold trajectoryCoordKernel
  exact Kernel.IsMarkovKernel.map _ measurable_up

/-- The genuine Ionescu–Tulcea trajectory law. There is no standard-Borel assumption on the seed. -/
def trajectoryLaw (ν : Measure Z) (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] : Measure (Π t, TrajectoryCoord Z O t) :=
  Kernel.trajMeasure (X := TrajectoryCoord Z O) (ν.map (ULift.up : Z → TrajectoryCoord Z O 0)) (trajectoryCoordKernel κ)

instance trajectoryLaw_probability (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) [∀ m, IsMarkovKernel (κ m)] :
    IsProbabilityMeasure (trajectoryLaw ν κ) := by
  have : IsProbabilityMeasure (ν.map (ULift.up : Z → TrajectoryCoord Z O 0)) := by
    constructor
    rw [Measure.map_apply measurable_up MeasurableSet.univ]
    simp
  unfold trajectoryLaw
  infer_instance

/-- Measurable input transport of a compProd; it needs no injectivity or regular conditional probability. -/
theorem map_compProd_comap {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [SFinite μ] (κ : Kernel B C) [IsSFiniteKernel κ] (f : A → B) (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs,
    Measure.compProd_apply ((hf.prodMap measurable_id) hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

/-- The initial marginal is exactly the original seed law, before any copy can be requested. -/
theorem trajectoryLaw_prefix_zero (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) [∀ m, IsMarkovKernel (κ m)] :
    (trajectoryLaw ν κ).map (trajectoryPrefix 0) = prefixLaw ν κ 0 := by
  have h0 : (trajectoryLaw ν κ).map (frestrictLe 0) =
      (ν.map (ULift.up : Z → TrajectoryCoord Z O 0)).map (MeasurableEquiv.piUnique (fun i : Iic (0:ℕ) => TrajectoryCoord Z O i)).symm := by
    rw [trajectoryLaw, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  change (trajectoryLaw ν κ).map (decodeTrajectoryPrefix 0 ∘ frestrictLe 0) = _
  rw [← Measure.map_map (decodeTrajectoryPrefix_measurable 0) (measurable_frestrictLe 0), h0,
    Measure.map_map (decodeTrajectoryPrefix_measurable 0) (MeasurableEquiv.piUnique (fun i : Iic (0:ℕ) => TrajectoryCoord Z O i)).symm.measurable]
  have he : decodeTrajectoryPrefix (Z := Z) (O := O) 0 ∘ (MeasurableEquiv.piUnique (fun i : Iic (0:ℕ) => TrajectoryCoord Z O i)).symm = id := by
    funext z
    rfl
  rw [he]
  change (ν.map (ULift.up : Z → ULift.{v} Z)).map id = ν.map ULift.up
  exact Measure.map_id

/-- Every finite marginal of the infinite trajectory is exactly the previously constructed prefix law. -/
theorem trajectoryLaw_prefix (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) [∀ m, IsMarkovKernel (κ m)] (m : ℕ) :
    (trajectoryLaw ν κ).map (trajectoryPrefix m) = prefixLaw ν κ m := by
  have : IsProbabilityMeasure (ν.map (ULift.up : Z → TrajectoryCoord Z O 0)) := by
    constructor
    rw [Measure.map_apply measurable_up MeasurableSet.univ]
    simp
  induction m with
  | zero => exact trajectoryLaw_prefix_zero ν κ
  | succ m ih =>
    change (trajectoryLaw ν κ).map (fun ω => (trajectoryPrefix m ω, (ω (m+1)).down)) =
      prefixLaw ν κ m ⊗ₘ κ m
    let F : (Π i : Iic m, TrajectoryCoord Z O i) × TrajectoryCoord Z O (m+1) → SlotHistory Z O m × Option O :=
      fun p => (decodeTrajectoryPrefix m p.1, p.2.down)
    have hF : Measurable F := (decodeTrajectoryPrefix_measurable m).prodMap measurable_down
    have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (μ₀ := ν.map (ULift.up : Z → TrajectoryCoord Z O 0)) (κ := trajectoryCoordKernel κ) (a := m)
    change (trajectoryLaw ν κ).map (frestrictLe m) ⊗ₘ trajectoryCoordKernel κ m =
      (trajectoryLaw ν κ).map (fun ω => (frestrictLe m ω, ω (m+1))) at h
    calc
      (trajectoryLaw ν κ).map (fun ω => (trajectoryPrefix m ω, (ω (m+1)).down)) =
          ((trajectoryLaw ν κ).map (frestrictLe m) ⊗ₘ trajectoryCoordKernel κ m).map F := by
        rw [h, Measure.map_map hF ((measurable_frestrictLe m).prodMk (measurable_pi_apply (m+1)))]
        rfl
      _ = ((trajectoryLaw ν κ).map (frestrictLe m) ⊗ₘ
          (κ m).comap (decodeTrajectoryPrefix m) (decodeTrajectoryPrefix_measurable m)).map
            (Prod.map (decodeTrajectoryPrefix m) id) := by
        rw [trajectoryCoordKernel, Measure.compProd_map measurable_up,
          Measure.map_map hF (measurable_id.prodMap measurable_up)]
        rfl
      _ = ((trajectoryLaw ν κ).map (frestrictLe m)).map (decodeTrajectoryPrefix m) ⊗ₘ κ m :=
        map_compProd_comap _ _ _ (decodeTrajectoryPrefix_measurable m)
      _ = prefixLaw ν κ m ⊗ₘ κ m := by
        rw [Measure.map_map (decodeTrajectoryPrefix_measurable m) (measurable_frestrictLe m)]
        change (trajectoryLaw ν κ).map (trajectoryPrefix m) ⊗ₘ κ m = _
        rw [ih]

end LocalCertification.Protocol
