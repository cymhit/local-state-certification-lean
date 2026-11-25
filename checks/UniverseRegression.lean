import LocalCertification.Paper
import LocalCertification.Protocol.MeasurableExecutionUniverse
import LocalCertification.Protocol.MeasurableExecutionProductTransport

open MeasureTheory LocalCertification.Protocol LocalCertification.Quantum
open LocalCertification.Protocol.MeasurableExecution
open scoped ENNReal
noncomputable section
namespace UniverseRegressionExamples

abbrev Outcome (_ : Fin 1) := ULift.{2} ℝ
abbrev Setting := ULift.{1} Unit

def localMeasurement : MeasurablePOVM (ULift.{2} ℝ) (Fin 1) :=
  (MeasurablePOVM.ofFinite (basisPOVM (1 : CertificationGaussian.LocalUnitary 1))).map
    (fun _ => ULift.up (0 : ℝ)) measurable_const

def stop : OriginalProductProtocol 1 1 ℝ Setting Outcome where
  rule _ _ := Sum.inl 0
  measurable_rule _ := measurable_const
  seedLaw := Measure.dirac 0
  seed_probability := inferInstance
  localFamilies _ := POVMKernel.constant localMeasurement

theorem stop_zero (p : OriginalProductProtocol.LiteralSample ℝ Outcome) : stop.time p = 0 := by
  apply le_antisymm _ zero_le
  apply (stoppingTime_le_iff stop.aligned.toRawRules (OriginalProductProtocol.sampleEquiv.{0,1,2} p) 0).mpr
  rintro ⟨v, hv⟩
  cases hv

example (ρ : QIT.State (CertificationGaussian.QuditIndex 1 1)) : stop.expectedCopies ρ = 0 := by
  change (∫⁻ p, ENat.toENNReal (stop.time p) ∂stop.law ρ) = 0
  simp only [stop_zero, ENat.toENNReal_zero, lintegral_zero]

def run : OriginalProductProtocol 1 1 ℝ Setting Outcome where
  rule _ _ := Sum.inr (ULift.up ())
  measurable_rule _ := measurable_const
  seedLaw := Measure.dirac 0
  seed_probability := inferInstance
  localFamilies _ := POVMKernel.constant localMeasurement

def path : OriginalProductProtocol.LiteralSample ℝ Outcome := (0, fun _ => Sum.inr (fun _ => ULift.up 0))

theorem run_active (m : ℕ) :
    PathActive run.aligned.toRawRules (OriginalProductProtocol.sampleEquiv.{0,1,2} path) m := by
  induction m with
  | zero => exact ⟨(Fin.elim0, ULift.up (ULift.up ())), rfl⟩
  | succ m ih =>
    obtain ⟨⟨h, s⟩, hh⟩ := ih
    change ∃ v, advance run.aligned.toRawRules _
      (state run.aligned.toRawRules m (rawPrefix m (OriginalProductProtocol.sampleEquiv.{0,1,2} path)))
      (Sum.inr (fun _ => ULift.up (ULift.up 0))) = Sum.inr v
    rw [hh]
    exact ⟨(Fin.snoc h (s, fun _ => ULift.up (ULift.up 0)), ULift.up (ULift.up ())), rfl⟩

theorem run_infinite : run.time path = ⊤ :=
  (MeasurableExecution.stoppingTime_eq_top_iff run.aligned.toRawRules _).mpr run_active

example (m : ℕ) : min (run.copyCost path) (m : ℝ≥0∞) = m := by
  change min (ENat.toENNReal (run.time path)) (m : ℝ≥0∞) = m
  rw [run_infinite, ENat.toENNReal_top, min_top_left]

example (N : ℕ) : ¬run.Capped N := by
  intro h
  have hp : run.Legal path := fun m => ⟨fun _ => run_active m, fun _ => ⟨_, rfl⟩⟩
  have ht := h path hp
  rw [run_infinite] at ht
  exact (not_le_of_gt (ENat.natCast_lt_top N)) ht

end UniverseRegressionExamples

#eval IO.println "UniverseRegression_PASS"
