import LocalCertification.Protocol.MeasurableExecutionLegality
import Mathlib.Probability.Process.Stopping

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information.KernelHistory
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u
variable {Z S Ω : Type u} [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω]

abbrev legalPaths (R : RawRules Z S Ω) := {p : Sample Z (Slot Ω) // Legal R p}

def forgetFullPrefix : ∀ m, FullHistory Z (Unit ⊕ (S × Ω)) m → History Z Ω m
  | 0 => id
  | m+1 => fun h => (forgetFullPrefix m h.1, Sum.map id Prod.snd h.2)

theorem forgetFullPrefix_measurable (m : ℕ) :
    Measurable (forgetFullPrefix (Z := Z) (S := S) (Ω := Ω) m) := by
  induction m with
  | zero => exact measurable_id
  | succ m ih =>
    exact (ih.comp measurable_fst).prodMk ((measurable_id.sumMap measurable_snd).comp measurable_snd)

theorem forgetFullPrefix_fullPrefix (R : RawRules Z S Ω) (m : ℕ)
    (p : Sample Z (Slot Ω)) (hp : Legal R p) :
    forgetFullPrefix m (fullPrefix R m (rawPrefix m p)) = rawPrefix m p := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact Prod.ext ih (labelSlot_recovers R m (rawPrefix m p) (p.2 m) (hp m))

/-- The original, uncompleted finite-history sigma algebra on every legal
path. No input law removes null seeds or null outcome branches. -/
@[instance_reducible] def legalPrefixSigma (R : RawRules Z S Ω) (m : ℕ) :
    MeasurableSpace (legalPaths R) :=
  MeasurableSpace.comap (fun p : legalPaths R => rawPrefix m p.val) inferInstance

theorem legalPrefixSigma_mono (R : RawRules Z S Ω) : Monotone (legalPrefixSigma R) := by
  apply monotone_nat_of_le_succ
  intro m
  exact MeasurableSpace.comap_le_comap_of_eq_comp
    (fun h : History Z Ω m × Slot Ω => h.1) measurable_fst rfl

def legalFiltration (R : RawRules Z S Ω) :
    Filtration ℕ (inferInstance : MeasurableSpace (legalPaths R)) where
  seq := legalPrefixSigma R
  mono' := legalPrefixSigma_mono R
  le' m := ((rawPrefix_measurable m).comp measurable_subtype_coe).comap_le

/-- Complete setting/outcome records generate exactly the same causal
filtration as the primitive slots, pointwise on all legal paths. -/
theorem legalPrefixSigma_eq_full (R : RawRules Z S Ω) (m : ℕ) :
    legalPrefixSigma R m = MeasurableSpace.comap
      (fun p : legalPaths R => fullPrefix R m (rawPrefix m p.val)) inferInstance := by
  apply le_antisymm
  · apply MeasurableSpace.comap_le_comap_of_eq_comp
      (forgetFullPrefix m) (forgetFullPrefix_measurable m)
    funext p
    exact (forgetFullPrefix_fullPrefix R m p.val p.property).symm
  · exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fullPrefix R m) (fullPrefix_measurable R m) rfl

theorem legal_stopped_measurable (R : RawRules Z S Ω) (m : ℕ) :
    MeasurableSet[legalFiltration R m]
      {p : legalPaths R | stoppingTime R p.val ≤ (m : ℕ∞)} := by
  have h := (comap_measurable (fun p : legalPaths R => rawPrefix m p.val))
    (active_measurable R m).compl
  have he : {p : legalPaths R | stoppingTime R p.val ≤ (m : ℕ∞)} =
      (fun p : legalPaths R => rawPrefix m p.val) ⁻¹' (active R m)ᶜ := by
    ext p
    exact stoppingTime_le_iff R p.val m
  rw [he]
  exact h

theorem legal_isStoppingTime (R : RawRules Z S Ω) :
    IsStoppingTime (legalFiltration R) (fun p => stoppingTime R p.val) := by
  intro m
  convert legal_stopped_measurable R m using 1
  rfl

theorem legal_stopped_decision_measurable (R : RawRules Z S Ω) (j : Fin 2) (m : ℕ) :
    MeasurableSet[legalFiltration R m]
      {p : legalPaths R | stoppingTime R p.val ≤ (m : ℕ∞) ∧ terminalDecision R p.val = j} := by
  have h := (comap_measurable (fun p : legalPaths R => rawPrefix m p.val))
    (prefixDecisionEvent_measurable R j m)
  have he : {p : legalPaths R | stoppingTime R p.val ≤ (m : ℕ∞) ∧ terminalDecision R p.val = j} =
      (fun p : legalPaths R => rawPrefix m p.val) ⁻¹' prefixDecisionEvent R j m := by
    ext p
    exact (prefixDecisionEvent_iff R p.val j m).symm
  rw [he]
  exact h

theorem exists_fullRecord_filtration (R : RawRules Z S Ω) :
    ∃ 𝓕 : Filtration ℕ (inferInstance : MeasurableSpace {p : Sample Z (Slot Ω) // Legal R p}),
      IsStoppingTime 𝓕 (fun p => stoppingTime R p.val) ∧
      (∀ m, 𝓕 m = MeasurableSpace.comap
        (fun p : {p : Sample Z (Slot Ω) // Legal R p} => rawPrefix m p.val) inferInstance) ∧
      (∀ m, 𝓕 m = MeasurableSpace.comap
        (fun p : {p : Sample Z (Slot Ω) // Legal R p} => fullPrefix R m (rawPrefix m p.val)) inferInstance) :=
  ⟨legalFiltration R, legal_isStoppingTime R, fun _ => rfl, legalPrefixSigma_eq_full R⟩

end LocalCertification.Protocol.MeasurableExecution
