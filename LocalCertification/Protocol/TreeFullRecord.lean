import LocalCertification.Protocol.TreeLaw

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- The complete public path retains its seed and every finite full-record state, including padding and decisions. -/
def fullRecordPath (R : RawRules Z S O) (p : RawSample Z O) : Z × ((m : ℕ) → ExecutionState S O m) :=
  (p.1, fun m => execPrefix R m (rawPrefix m p))

omit [MeasurableSingletonClass O] in
theorem fullRecordPath_measurable (R : RawRules Z S O) : Measurable (fullRecordPath R) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun m => (execPrefix_measurable R m).comp (rawPrefix_measurable m)))

/-- On consistent paths every full record is identical; only the retained seed is mapped to its tree. -/
theorem fullRecordPath_tree_map (R : RawRules Z S O) (p : RawSample Z O)
    (hc : ∀ m, ConsistentPrefix R m (rawPrefix m p)) :
    fullRecordPath (treeRules (seedTreeImage R)) (mapRawSeed (seedToTree R) p) =
      Prod.map (seedToTree R) id (fullRecordPath R p) := by
  apply Prod.ext
  · rfl
  · funext m
    change execPrefix (treeRules (seedTreeImage R)) m (rawPrefix m (mapRawSeed (seedToTree R) p)) =
      execPrefix R m (rawPrefix m p)
    rw [← mapSlotSeed_rawPrefix]
    exact treeRules_execPrefix_map R m (rawPrefix m p) (hc m)

variable {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- Equality of complete infinite public-record laws, with old seeds explicitly pushed to their tree image. -/
theorem imageTreeProtocol_fullRecordLaw (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (executionLaw (imageTreeProtocol P) ρ).map (fullRecordPath (imageTreeProtocol P).toRawRules) =
      ((executionLaw P ρ).map (fullRecordPath P.toRawRules)).map
        (Prod.map (seedToTree P.toRawRules) id) := by
  rw [← imageTreeProtocol_executionLaw,
    Measure.map_map (fullRecordPath_measurable _) (mapRawSeed_measurable _ (seedToTree_measurable P.toRawRules)),
    Measure.map_map ((seedToTree_measurable P.toRawRules).prodMap measurable_id) (fullRecordPath_measurable _)]
  apply Measure.map_congr
  filter_upwards [executionLaw_ae_consistent P ρ] with p hp
  exact fullRecordPath_tree_map P.toRawRules p hp

end LocalCertification.Protocol
