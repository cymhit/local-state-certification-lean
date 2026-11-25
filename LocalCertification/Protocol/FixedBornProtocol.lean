import LocalCertification.Protocol.FixedSamplingLaw
import LocalCertification.Protocol.BornTrajectory

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical Set LocalCertification.Information LocalCertification.Quantum
open scoped BigOperators ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {H : Type u} [MeasurableSpace H] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- A genuine qudit RawProtocol with all labels sampled before the copies and the specified complete-record test. -/
def fixedBornProtocol (N : ℕ) (setting : H → ProductSetting d n) (hs : Measurable setting)
    (verdict : (Fin N → H × CertificationGaussian.QuditIndex d n) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ] : QuditProtocol (Fin N → H) d n :=
  fixedHorizonProtocol N setting hs verdict hv μ

/-- The actual full labels and outcomes read from the original execution space. -/
def fixedBornRecords (N : ℕ) (p : RawSample (Fin N → H) (CertificationGaussian.QuditIndex d n)) :
    Fin N → H × CertificationGaussian.QuditIndex d n := fun i => (p.1 i,(p.2 i.val).getD default)

theorem fixedBornRecords_measurable (N : ℕ) : Measurable (fixedBornRecords (H:=H) (d:=d) (n:=n) N) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_of_countable (fun x : Option (CertificationGaussian.QuditIndex d n) => x.getD default)).comp
      ((measurable_pi_apply i.val).comp measurable_snd))

/-- Every path stops after precisely N copies, including null seeds and null outcome branches. -/
theorem fixedBornProtocol_executionTime (N : ℕ) (setting : H → ProductSetting d n) (hs : Measurable setting)
    (verdict : (Fin N → H × CertificationGaussian.QuditIndex d n) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (p : RawSample (Fin N → H) (CertificationGaussian.QuditIndex d n)) :
    executionTime (fixedBornProtocol N setting hs verdict hv μ) p = (N : WithTop ℕ) :=
  fixedHorizon_stoppingTime N setting hs verdict hv p.1 (fun m => (p.2 m).getD default)

theorem fixedBornProtocol_capped (N : ℕ) (setting : H → ProductSetting d n) (hs : Measurable setting)
    (verdict : (Fin N → H × CertificationGaussian.QuditIndex d n) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ] : Capped (fixedBornProtocol N setting hs verdict hv μ) N :=
  fixedHorizon_everyPathCap N setting hs verdict hv

theorem fixedBornProtocol_decision (N : ℕ) (setting : H → ProductSetting d n) (hs : Measurable setting)
    (verdict : (Fin N → H × CertificationGaussian.QuditIndex d n) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (p : RawSample (Fin N → H) (CertificationGaussian.QuditIndex d n)) :
    executionDecision (fixedBornProtocol N setting hs verdict hv μ) p = verdict (fixedBornRecords N p) :=
  fixedHorizon_terminalDecision N setting hs verdict hv p.1 (fun m => (p.2 m).getD default)

/-- Actual expected cost is exactly the fixed cap for every mixed input, with N=0 retained. -/
theorem fixedBornProtocol_expectedCopies (N : ℕ) (setting : H → ProductSetting d n) (hs : Measurable setting)
    (verdict : (Fin N → H × CertificationGaussian.QuditIndex d n) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ] (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    expectedCopies (fixedBornProtocol N setting hs verdict hv μ) ρ = (N : ℝ≥0∞) := by
  have hc (p : RawSample (Fin N → H) (CertificationGaussian.QuditIndex d n)) :
      executionCost (fixedBornProtocol N setting hs verdict hv μ) p = (N : ℝ≥0∞) := by
    change ENat.toENNReal (executionTime (fixedBornProtocol N setting hs verdict hv μ) p) = _
    rw [fixedBornProtocol_executionTime]
    rfl
  simp only [expectedCopies, hc, lintegral_const, measure_univ, mul_one]

/-- The actual N-prefix is identified with the proved conditional product sampling model. -/
theorem fixedBornProtocol_prefixLaw (N : ℕ) (setting : H → ProductSetting d n) (hs : Measurable setting)
    (verdict : (Fin N → H × CertificationGaussian.QuditIndex d n) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ] (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    ((Measure.pi (fun _ : Fin N => μ)) ⊗ₘ
      finiteProductKernel (controlledProductBornKernel d n ρ setting hs)).map
      (fixedWordPrefix N setting hs verdict hv N) =
      executionPrefixLaw (fixedBornProtocol N setting hs verdict hv μ) ρ N :=
  fixedSamplingLaw_prefix N setting hs verdict hv (productBornKernel d n ρ)
    (Measure.pi (fun _ : Fin N => μ)) N le_rfl

omit [MeasurableSpace H] in
/-- A literal finite decoder, not an assumed inverse of arbitrary stopped public records. -/
theorem fixedWordDecode_rawPrefix (N : ℕ)
    (p : RawSample (Fin N → H) (CertificationGaussian.QuditIndex d n)) :
    fixedWordDecode N (rawPrefix N p) = (p.1,fun i : Fin N => (p.2 i.val).getD default) := by
  apply Prod.ext
  · exact slotSeed_rawPrefix N p
  · funext i
    simp only [fixedWordDecode, historySlot_rawPrefix]

/-- Under the actual infinite Born executor, the complete N records have the genuine iid one-copy Born law. -/
theorem fixedBornProtocol_records_law (N : ℕ) (setting : H → ProductSetting d n) (hs : Measurable setting)
    (verdict : (Fin N → H × CertificationGaussian.QuditIndex d n) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ] (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (executionLaw (fixedBornProtocol N setting hs verdict hv μ) ρ).map (fixedBornRecords N) =
      Measure.pi (fun _ : Fin N => completeBornRecordLaw ρ setting hs μ) := by
  let P := fixedBornProtocol N setting hs verdict hv μ
  let Q := (Measure.pi (fun _ : Fin N => μ)) ⊗ₘ finiteProductKernel (controlledProductBornKernel d n ρ setting hs)
  have hd : (executionPrefixLaw P ρ N).map (fixedWordDecode N) = Q := by
    rw [← fixedBornProtocol_prefixLaw N setting hs verdict hv μ ρ,
      Measure.map_map (fixedWordDecode_measurable N) (fixedWordPrefix_measurable N setting hs verdict hv N),
      show fixedWordDecode N ∘ fixedWordPrefix N setting hs verdict hv N = id from
        funext (fixedWordDecode_prefix N setting hs verdict hv), Measure.map_id]
  have hr : (executionLaw P ρ).map (fun p => (p.1,fun i : Fin N => (p.2 i.val).getD default)) = Q := by
    rw [← hd, ← executionLaw_prefix P ρ N,
      Measure.map_map (fixedWordDecode_measurable N) (rawPrefix_measurable N)]
    congr 1
    funext p
    exact (fixedWordDecode_rawPrefix N p).symm
  have hzip := congrArg (fun ξ => ξ.map (fun p => fun i => (p.1 i,p.2 i))) hr
  have hm : Measurable (fun p : RawSample (Fin N → H) (CertificationGaussian.QuditIndex d n) =>
      (p.1,fun i : Fin N => (p.2 i.val).getD default)) :=
    measurable_fst.prodMk (measurable_pi_iff.mpr (fun i =>
      (measurable_of_countable (fun o : Option (CertificationGaussian.QuditIndex d n) => o.getD default)).comp
        ((measurable_pi_apply i.val).comp measurable_snd)))
  rw [Measure.map_map completeRecords_measurable hm] at hzip
  dsimp only [Q] at hzip
  rw [independent_complete_records] at hzip
  exact hzip

/-- Every error event of the actual raw protocol is exactly the event of its iid complete-record test. -/
theorem fixedBornProtocol_error (N : ℕ) (setting : H → ProductSetting d n) (hs : Measurable setting)
    (verdict : (Fin N → H × CertificationGaussian.QuditIndex d n) → Fin 2) (hv : Measurable verdict)
    (μ : Measure H) [IsProbabilityMeasure μ] (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : Fin 2) :
    executionLaw (fixedBornProtocol N setting hs verdict hv μ) ρ
      {p | executionDecision (fixedBornProtocol N setting hs verdict hv μ) p = j} =
      (Measure.pi (fun _ : Fin N => completeBornRecordLaw ρ setting hs μ)) {x | verdict x = j} := by
  rw [← fixedBornProtocol_records_law N setting hs verdict hv μ ρ]
  erw [Measure.map_apply (fixedBornRecords_measurable N)
    (show MeasurableSet {x | verdict x = j} from hv (measurableSet_singleton j))]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, fixedBornProtocol_decision]

end LocalCertification.Protocol
