import LocalCertification.Protocol.SeedTransport
import LocalCertification.Protocol.BornTrajectory

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- The canonical protocol uses precisely the full tree image and the pushed common seed law. -/
def imageTreeProtocol (P : QuditProtocol Z d n) :
    QuditProtocol (seedTreeImage P.toRawRules) d n where
  toRawRules := treeRules (seedTreeImage P.toRawRules)
  seedLaw := P.seedLaw.map (seedToTree P.toRawRules)
  seed_probability := by
    constructor
    rw [Measure.map_apply (seedToTree_measurable P.toRawRules) MeasurableSet.univ]
    simp

/-- The actual next Born kernel agrees pointwise on every consistent prefix, for every physical input. -/
theorem imageTreeProtocol_kernel (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ)
    (h : SlotHistory Z (CertificationGaussian.QuditIndex d n) m) (hc : ConsistentPrefix P.toRawRules m h) :
    executionSlotKernel (imageTreeProtocol P) ρ m (mapSlotSeed (seedToTree P.toRawRules) m h) =
      executionSlotKernel P ρ m h := by
  have he := treeRules_execPrefix_map P.toRawRules m h hc
  simp only [executionSlotKernel, stopContinue_apply, controlledProductBornKernel_apply,
    imageTreeProtocol, activePrefix, Set.mem_ofPred_eq, prefixSetting]
  simp only [he]
  split_ifs <;> rfl

/-- Explicit finite-kernel induction transports every actual prefix law. No seed disintegration is used. -/
theorem imageTreeProtocol_prefixLaw (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    (executionPrefixLaw P ρ m).map (mapSlotSeed (seedToTree P.toRawRules) m) =
      executionPrefixLaw (imageTreeProtocol P) ρ m := by
  induction m with
  | zero =>
    change (P.seedLaw.map (ULift.up : Z → ULift.{0} Z)).map
      (fun h : ULift.{0} Z => (ULift.up (seedToTree P.toRawRules h.down) : ULift.{0} (seedTreeImage P.toRawRules))) =
      (P.seedLaw.map (seedToTree P.toRawRules)).map
        (ULift.up : seedTreeImage P.toRawRules → ULift.{0} (seedTreeImage P.toRawRules))
    have hf : Measurable (fun h : ULift.{0} Z =>
        (ULift.up (seedToTree P.toRawRules h.down) : ULift.{0} (seedTreeImage P.toRawRules))) :=
      measurable_up.comp ((seedToTree_measurable P.toRawRules).comp measurable_down)
    exact (Measure.map_map hf measurable_up).trans
      (Measure.map_map (g := (ULift.up : seedTreeImage P.toRawRules → ULift.{0} (seedTreeImage P.toRawRules)))
        measurable_up (seedToTree_measurable P.toRawRules)).symm

  | succ m ih =>
    let f := mapSlotSeed (O := CertificationGaussian.QuditIndex d n) (seedToTree P.toRawRules) m
    have hf : Measurable f := mapSlotSeed_measurable _ (seedToTree_measurable P.toRawRules) m
    have hk : executionSlotKernel P ρ m =ᵐ[executionPrefixLaw P ρ m]
        (executionSlotKernel (imageTreeProtocol P) ρ m).comap f hf := by
      filter_upwards [executionPrefixLaw_ae_consistent P ρ m] with h hh
      exact (imageTreeProtocol_kernel P ρ m h hh).symm
    change (executionPrefixLaw P ρ m ⊗ₘ executionSlotKernel P ρ m).map (Prod.map f id) =
      executionPrefixLaw (imageTreeProtocol P) ρ m ⊗ₘ executionSlotKernel (imageTreeProtocol P) ρ m
    rw [Measure.compProd_congr hk, map_compProd_comap _ _ f hf, ih]

/-- The full image includes all original seeds, hence every-path caps are equivalent for every N. -/
theorem imageTreeProtocol_capped_iff (P : QuditProtocol Z d n) (N : ℕ) :
    Capped (imageTreeProtocol P) N ↔ Capped P N :=
  treeRules_everyPathCap_iff P.toRawRules N

end LocalCertification.Protocol
