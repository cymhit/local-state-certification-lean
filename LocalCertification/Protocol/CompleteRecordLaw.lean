import LocalCertification.Protocol.LegalPaths
import LocalCertification.Protocol.FullRecord

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- A global measurable decoder from complete public paths to primitive slots; its inverse identity is restricted to legal paths. -/
def decodeFullRecordPath (q : Z × ((m : ℕ) → ExecutionState S O m)) : RawSample Z O :=
  (q.1, fun m => (decodePublicPrefix (m+1) (q.1,q.2 (m+1))).2)

omit [Inhabited S] [Inhabited O] in
theorem decodeFullRecordPath_measurable : Measurable (decodeFullRecordPath (Z := Z) (S := S) (O := O)) := by
  apply measurable_fst.prodMk
  apply measurable_pi_iff.mpr
  intro m
  exact measurable_snd.comp ((decodePublicPrefix_measurable (m+1)).comp
    (measurable_fst.prodMk ((measurable_pi_apply (m+1)).comp measurable_snd)))

omit [Fintype O] [MeasurableSingletonClass O] in
/-- Every legal path has a pointwise complete-record left inverse, including all null seeds and branches. -/
theorem decodeFullRecordPath_leftInverse (R : RawRules Z S O) (p : legalPaths R) :
    decodeFullRecordPath (fullRecordPath R p.val) = p.val := by
  apply Prod.ext
  · rfl
  · funext m
    have h := decodePublicPrefix_publicPrefix R (m+1) (rawPrefix (m+1) p.val) (p.property (m+1))
    change decodePublicPrefix (m+1) (slotSeed (m+1) (rawPrefix (m+1) p.val),
      execPrefix R (m+1) (rawPrefix (m+1) p.val)) = rawPrefix (m+1) p.val at h
    rw [slotSeed_rawPrefix] at h
    exact congrArg (fun h : SlotHistory Z O m × Option O => h.2) h

variable {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- Complete infinite records and the original primitive execution have exactly the same full singular KL. -/
theorem fullRecordPath_klDiv (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    klDiv ((executionLaw P ρ).map (fullRecordPath P.toRawRules))
      ((executionLaw P σ).map (fullRecordPath P.toRawRules)) = klDiv (executionLaw P ρ) (executionLaw P σ) := by
  apply klDiv_map_retract_ae _ _ (fullRecordPath P.toRawRules) decodeFullRecordPath
    (fullRecordPath_measurable P.toRawRules) decodeFullRecordPath_measurable
  · filter_upwards [executionLaw_ae_consistent P ρ] with p hp
    exact decodeFullRecordPath_leftInverse P.toRawRules ⟨p,hp⟩
  · filter_upwards [executionLaw_ae_consistent P σ] with p hp
    exact decodeFullRecordPath_leftInverse P.toRawRules ⟨p,hp⟩

end LocalCertification.Protocol
