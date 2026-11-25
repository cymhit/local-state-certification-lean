import LocalCertification.Quantum.HaarMeasurement
import CertificationGaussian.Consumers.PauliLocalReadout

set_option autoImplicit false
open Matrix Classical MeasureTheory CertificationGaussian
open scoped BigOperators ComplexOrder ENNReal
noncomputable section
namespace LocalCertification.Quantum

/-- The true QIT effect of the Z/X/Y basis and outcome is the existing six-record projector. -/
theorem basisPOVM_pauliRecordedProjector (ω : PauliRecord) :
    (basisPOVM (pauliBasisUnitary ω.1)).effects ω.2 = pauliRecordedProjector ω :=
  basisPOVM_recordedProjector 2 (pauliFullRecord ω)

/-- Actual finite Pauli reference records have both local twirls for arbitrary complex matrices. -/
theorem qit_pauli_record_twirl (A : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    ((2:ℂ) * ∫ ω, (basisPOVM (pauliBasisUnitary ω.1)).effects ω.2 a b *
      Matrix.trace ((basisPOVM (pauliBasisUnitary ω.1)).effects ω.2 * A) ∂pauliBasisRecords =
      (A a b + if a=b then Matrix.trace A else 0)/3) ∧
    ((2:ℂ) * ∫ ω, (basisPOVM (pauliBasisUnitary ω.1)).effects ω.2 a b *
      Matrix.trace ((1-(basisPOVM (pauliBasisUnitary ω.1)).effects ω.2) * A) ∂pauliBasisRecords =
      ((if a=b then 2*Matrix.trace A else 0)-A a b)/3) := by
  simp_rw [basisPOVM_pauliRecordedProjector]
  exact CertificationGaussian.Consumers.pauli_actual_twirls A a b

/-- All finite complete-record functions are genuinely integrable under the reference probability law. -/
theorem pauli_reference_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : PauliRecord → E) : Integrable f pauliBasisRecords :=
  (show Continuous f from continuous_of_discreteTopology).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The state-dependent density relative to uniform basis and uniform outcome is exactly 2p. -/
def pauliBornDensity (ρ : QIT.State (Fin 2)) (ω : PauliRecord) : ℝ :=
  2 * basisBorn (pauliBasisUnitary ω.1) ρ ω.2

theorem pauliBornDensity_nonneg (ρ : QIT.State (Fin 2)) (ω : PauliRecord) :
    0 ≤ pauliBornDensity ρ ω := mul_nonneg (by norm_num) (basisBorn_nonneg _ _ _)

theorem pauliBornDensity_continuous (ρ : QIT.State (Fin 2)) : Continuous (pauliBornDensity ρ) :=
  continuous_of_discreteTopology

theorem pauliBornDensity_integrable (ρ : QIT.State (Fin 2)) :
    Integrable (pauliBornDensity ρ) pauliBasisRecords := pauli_reference_integrable _

theorem pauliBornDensity_integral (ρ : QIT.State (Fin 2)) :
    ∫ ω, pauliBornDensity ρ ω ∂pauliBasisRecords = 1 := by
  rw [pauliBasisRecords_integral]
  simp only [pauliBornDensity, ← Finset.mul_sum, basisBorn_sum]
  norm_num

/-- This is the actual Born law on all six complete Pauli basis/outcome records. -/
def pauliBornRecordLaw (ρ : QIT.State (Fin 2)) : Measure PauliRecord :=
  pauliBasisRecords.withDensity (fun ω => ENNReal.ofReal (pauliBornDensity ρ ω))

instance pauliBornRecordLaw_probability (ρ : QIT.State (Fin 2)) :
    IsProbabilityMeasure (pauliBornRecordLaw ρ) where
  measure_univ := by
    rw [pauliBornRecordLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (pauliBornDensity_integrable ρ)
        (Filter.Eventually.of_forall (pauliBornDensity_nonneg ρ)), pauliBornDensity_integral]
    simp

/-- Each literal basis/outcome atom has uniform basis mass times its actual QIT Born probability. -/
theorem pauliBornRecordLaw_singleton (ρ : QIT.State (Fin 2)) (ω : PauliRecord) :
    pauliBornRecordLaw ρ {ω} = (1/3:ℝ≥0∞) * ENNReal.ofReal (basisBorn (pauliBasisUnitary ω.1) ρ ω.2) := by
  rw [pauliBornRecordLaw, withDensity_apply _ (measurableSet_singleton ω),
    lintegral_singleton, CertificationGaussian.Consumers.pauli_record_mass, pauliBornDensity,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  calc
    _ = ((2:ℝ≥0∞)*(1/6)) * ENNReal.ofReal (basisBorn (pauliBasisUnitary ω.1) ρ ω.2) := by
      exact mul_right_comm (2:ℝ≥0∞) _ _
    _ = _ := by
      have hc : (2:ℝ≥0∞)*(1/6) = 1/3 := by
        rw [one_div, show (6:ℝ≥0∞)=2*3 by norm_num,
          ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        simp only [one_div]
      rw [hc]

/-- The Born-law integral is the actual reference-law integral weighted by 2p. -/
theorem pauliBornRecordLaw_integral (ρ : QIT.State (Fin 2)) (f : PauliRecord → ℂ) :
    ∫ ω, f ω ∂pauliBornRecordLaw ρ =
      ∫ ω, pauliBornDensity ρ ω • f ω ∂pauliBasisRecords := by
  rw [pauliBornRecordLaw, integral_withDensity_eq_integral_toReal_smul
    (pauliBornDensity_continuous ρ).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (pauliBornDensity_nonneg ρ _)]

theorem pauliBornRecordLaw_projector_integrable (ρ : QIT.State (Fin 2)) (a b : Fin 2) :
    Integrable (fun ω => (basisPOVM (pauliBasisUnitary ω.1)).effects ω.2 a b) (pauliBornRecordLaw ρ) :=
  (show Continuous _ from continuous_of_discreteTopology).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The genuine Born-law mean effect is (rho+I)/3, and is not the reference mean I/2. -/
theorem pauliBornRecordLaw_projector_mean (ρ : QIT.State (Fin 2)) (a b : Fin 2) :
    ∫ ω, (basisPOVM (pauliBasisUnitary ω.1)).effects ω.2 a b ∂pauliBornRecordLaw ρ =
      (ρ.matrix a b + if a=b then 1 else 0)/3 := by
  rw [pauliBornRecordLaw_integral]
  calc
    _ = (2:ℂ) * ∫ ω, (basisPOVM (pauliBasisUnitary ω.1)).effects ω.2 a b *
        (basisBorn (pauliBasisUnitary ω.1) ρ ω.2 : ℂ) ∂pauliBasisRecords := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [pauliBornDensity, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    _ = _ := by
      have he (ω : PauliRecord) : (basisBorn (pauliBasisUnitary ω.1) ρ ω.2 : ℂ) =
          ((basisPOVM (pauliBasisUnitary ω.1)).effects ω.2 * ρ.matrix).trace := by
        rw [basisBorn_complex_trace, Matrix.trace_mul_comm]
      simp_rw [he]
      simpa only [ρ.trace_eq_one] using (qit_pauli_record_twirl ρ.matrix a b).1

end LocalCertification.Quantum
