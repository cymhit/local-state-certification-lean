import LocalCertification.Information.KernelHistory
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! Actual Ionescu--Tulcea execution on arbitrary measurable seeds and ordered
records. No finite, countable, standard-Borel or canonical-tree assumption. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Function Finset Preorder
  LocalCertification.Information.KernelHistory
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

abbrev Coord (Z Ω : Type u) : ℕ → Type u
  | 0 => Z
  | _+1 => Ω

variable {Z Ω : Type u} [MeasurableSpace Z] [MeasurableSpace Ω]

@[reducible] instance coordMeasurable : (n : ℕ) → MeasurableSpace (Coord Z Ω n)
  | 0 => inferInstanceAs (MeasurableSpace Z)
  | _+1 => inferInstanceAs (MeasurableSpace Ω)

def decodePrefix : ∀ n, (Π i : Iic n, Coord Z Ω i) → FullHistory Z Ω n
  | 0 => fun f => f ⟨0, by simp⟩
  | n+1 => fun f => (decodePrefix n (frestrictLe₂ (Nat.le_succ n) f), f ⟨n+1, by simp⟩)

theorem decodePrefix_measurable (n : ℕ) : Measurable (decodePrefix (Z := Z) (Ω := Ω) n) := by
  induction n with
  | zero => exact measurable_pi_apply (⟨0, by simp⟩ : Iic (0 : ℕ))
  | succ n ih =>
    exact (ih.comp (measurable_frestrictLe₂ _)).prodMk
      (measurable_pi_apply (⟨n+1, by simp⟩ : Iic (n+1)))

def trajectoryPrefix (n : ℕ) (ω : Π t, Coord Z Ω t) : FullHistory Z Ω n :=
  decodePrefix n (frestrictLe n ω)

theorem trajectoryPrefix_measurable (n : ℕ) :
    Measurable (trajectoryPrefix (Z := Z) (Ω := Ω) n) :=
  (decodePrefix_measurable n).comp (measurable_frestrictLe n)

def coordKernel (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) (n : ℕ) :
    Kernel (Π i : Iic n, Coord Z Ω i) (Coord Z Ω (n+1)) :=
  (κ n).comap (decodePrefix n) (decodePrefix_measurable n)

instance coordKernel_markov (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) : IsMarkovKernel (coordKernel κ n) := by
  unfold coordKernel
  infer_instance

/-- The law is the library's actual trajectory measure, not an assumed family
of consistent finite laws or a regular conditional probability construction. -/
def trajectoryLaw (seed : Measure Z) (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω)
    [∀ n, IsMarkovKernel (κ n)] : Measure (Π t, Coord Z Ω t) :=
  Kernel.trajMeasure (X := Coord Z Ω) seed (coordKernel κ)

instance trajectoryLaw_probability (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) [∀ n, IsMarkovKernel (κ n)] :
    IsProbabilityMeasure (trajectoryLaw seed κ) := by
  unfold trajectoryLaw
  infer_instance

private theorem map_compProd_comap {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [SFinite μ] (κ : Kernel B C) [IsSFiniteKernel κ]
    (f : A → B) (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs,
    Measure.compProd_apply ((hf.prodMap measurable_id) hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

theorem trajectoryLaw_prefix_zero (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) [∀ n, IsMarkovKernel (κ n)] :
    (trajectoryLaw seed κ).map (trajectoryPrefix 0) = seed := by
  have h0 : (trajectoryLaw seed κ).map (frestrictLe 0) =
      seed.map (MeasurableEquiv.piUnique (fun i : Iic (0 : ℕ) => Coord Z Ω i)).symm := by
    rw [trajectoryLaw, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  change (trajectoryLaw seed κ).map (decodePrefix 0 ∘ frestrictLe 0) = _
  rw [← Measure.map_map (decodePrefix_measurable 0) (measurable_frestrictLe 0), h0,
    Measure.map_map (decodePrefix_measurable 0)
      (MeasurableEquiv.piUnique (fun i : Iic (0 : ℕ) => Coord Z Ω i)).symm.measurable]
  have he : decodePrefix (Z := Z) (Ω := Ω) 0 ∘
      (MeasurableEquiv.piUnique (fun i : Iic (0 : ℕ) => Coord Z Ω i)).symm = id := by
    funext z; rfl
  rw [he]
  change seed.map (id : Z → Z) = seed
  exact Measure.map_id

/-- Every finite marginal is exactly the seeded iterated compProd law used by
the general information recursion, with the same ordered complete records. -/
theorem trajectoryLaw_prefix (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (trajectoryLaw seed κ).map (trajectoryPrefix n) = prefixLaw seed κ n := by
  induction n with
  | zero => exact trajectoryLaw_prefix_zero seed κ
  | succ n ih =>
    change (trajectoryLaw seed κ).map (fun ω => (trajectoryPrefix n ω, ω (n+1))) =
      prefixLaw seed κ n ⊗ₘ κ n
    let F : (Π i : Iic n, Coord Z Ω i) × Coord Z Ω (n+1) → FullHistory Z Ω n × Ω :=
      Prod.map (decodePrefix n) id
    have hF : Measurable F := (decodePrefix_measurable n).prodMap measurable_id
    have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (μ₀ := seed) (κ := coordKernel κ) (a := n)
    change (trajectoryLaw seed κ).map (frestrictLe n) ⊗ₘ coordKernel κ n =
      (trajectoryLaw seed κ).map (fun ω => (frestrictLe n ω, ω (n+1))) at h
    calc
      _ = ((trajectoryLaw seed κ).map (frestrictLe n) ⊗ₘ coordKernel κ n).map F := by
        rw [h, Measure.map_map hF ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1)))]
        rfl
      _ = ((trajectoryLaw seed κ).map (frestrictLe n)).map (decodePrefix n) ⊗ₘ κ n :=
        map_compProd_comap _ _ _ (decodePrefix_measurable n)
      _ = _ := by
        rw [Measure.map_map (decodePrefix_measurable n) (measurable_frestrictLe n)]
        exact congrArg (fun μ => μ ⊗ₘ κ n) ih

/-- Literal original seed and record stream: no quotient or deleted null path. -/
abbrev Sample (Z Ω : Type u) := Z × (ℕ → Ω)

def pack (p : Sample Z Ω) : Π t, Coord Z Ω t
  | 0 => p.1
  | n+1 => p.2 n

def unpack (ω : Π t, Coord Z Ω t) : Sample Z Ω := (ω 0, fun n => ω (n+1))

theorem pack_measurable : Measurable (pack (Z := Z) (Ω := Ω)) := by
  apply measurable_pi_iff.mpr
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

theorem unpack_measurable : Measurable (unpack (Z := Z) (Ω := Ω)) :=
  (measurable_pi_apply 0).prodMk (measurable_pi_iff.mpr (fun n => measurable_pi_apply (n+1)))

def sampleEquiv : (Π t, Coord Z Ω t) ≃ᵐ Sample Z Ω where
  toFun := unpack
  invFun := pack
  left_inv := by intro ω; funext n; cases n <;> rfl
  right_inv := fun _ => rfl
  measurable_toFun := unpack_measurable
  measurable_invFun := pack_measurable

def rawPrefix : ∀ n, Sample Z Ω → FullHistory Z Ω n
  | 0 => Prod.fst
  | n+1 => fun p => (rawPrefix n p, p.2 n)

theorem rawPrefix_measurable (n : ℕ) : Measurable (rawPrefix (Z := Z) (Ω := Ω) n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih => exact ih.prodMk ((measurable_pi_apply n).comp measurable_snd)

omit [MeasurableSpace Z] [MeasurableSpace Ω] in
theorem rawPrefix_unpack (n : ℕ) (ω : Π t, Coord Z Ω t) :
    rawPrefix n (unpack ω) = trajectoryPrefix n ω := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun h => (h, ω (n+1))) ih

def executionLaw (seed : Measure Z) (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω)
    [∀ n, IsMarkovKernel (κ n)] : Measure (Sample Z Ω) :=
  (trajectoryLaw seed κ).map unpack

instance executionLaw_probability (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) [∀ n, IsMarkovKernel (κ n)] :
    IsProbabilityMeasure (executionLaw seed κ) := by
  constructor
  rw [executionLaw, Measure.map_apply unpack_measurable MeasurableSet.univ]
  simp

theorem executionLaw_prefix (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (executionLaw seed κ).map (rawPrefix n) = prefixLaw seed κ n := by
  rw [executionLaw, Measure.map_map (rawPrefix_measurable n) unpack_measurable]
  have he : rawPrefix (Z := Z) (Ω := Ω) n ∘ unpack = trajectoryPrefix n :=
    funext (rawPrefix_unpack n)
  rw [he, trajectoryLaw_prefix]

theorem executionLaw_seed (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) [∀ n, IsMarkovKernel (κ n)] :
    (executionLaw seed κ).map Prod.fst = seed := executionLaw_prefix seed κ 0

theorem exists_executionLaw (seed : Measure Z) [IsProbabilityMeasure seed]
    (κ : ∀ n, Kernel (FullHistory Z Ω n) Ω) [∀ n, IsMarkovKernel (κ n)] :
    ∃ law : Measure (Z × (ℕ → Ω)), IsProbabilityMeasure law ∧
      law.map Prod.fst = seed ∧ ∀ n, law.map (rawPrefix n) = prefixLaw seed κ n :=
  ⟨executionLaw seed κ, inferInstance, executionLaw_seed seed κ, executionLaw_prefix seed κ⟩

end LocalCertification.Protocol.MeasurableExecution
