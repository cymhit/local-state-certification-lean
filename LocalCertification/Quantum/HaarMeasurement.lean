import LocalCertification.Quantum.ProductMeasurement
import CertificationGaussian.Consumers.LocalHaarTwirl

open scoped BigOperators ComplexOrder ENNReal
open Matrix Classical MeasureTheory
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

/-- The actual QIT measurement effect equals the projector on the full Haar basis/outcome record. -/
theorem basisPOVM_recordedProjector (d : ℕ) (ω : CertificationGaussian.ComplexUnitary (Fin d) × Fin d) :
    (basisPOVM ω.1).effects ω.2 = CertificationGaussian.recordedProjector d ω := by
  rw [basisPOVM_effect, CertificationGaussian.Consumers.haar_record_coordinate_effect]

/-- Reference Haar-times-uniform records, with the paper's exact factor d. -/
theorem qit_haar_record_twirl (d : ℕ) [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    ((d : ℂ) * ∫ ω, (basisPOVM ω.1).effects ω.2 a b *
        Matrix.trace ((basisPOVM ω.1).effects ω.2 * A) ∂CertificationGaussian.haarBasisRecords d =
      (A a b + if a = b then Matrix.trace A else 0) / ((d : ℂ)+1)) ∧
    ((d : ℂ) * ∫ ω, (basisPOVM ω.1).effects ω.2 a b *
        Matrix.trace ((1-(basisPOVM ω.1).effects ω.2) * A) ∂CertificationGaussian.haarBasisRecords d =
      (((d : ℂ)*Matrix.trace A)*(if a=b then 1 else 0)-A a b) / ((d : ℂ)+1)) := by
  simp_rw [basisPOVM_recordedProjector]
  exact CertificationGaussian.Consumers.local_haar_twirl_pair d A a b

theorem qit_haar_record_twirl_integrable (d : ℕ) [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    Integrable (fun ω => (basisPOVM ω.1).effects ω.2 a b *
      Matrix.trace ((basisPOVM ω.1).effects ω.2 * A)) (CertificationGaussian.haarBasisRecords d) ∧
    Integrable (fun ω => (basisPOVM ω.1).effects ω.2 a b *
      Matrix.trace ((1-(basisPOVM ω.1).effects ω.2) * A)) (CertificationGaussian.haarBasisRecords d) := by
  simp_rw [basisPOVM_recordedProjector]
  exact CertificationGaussian.haarBasisRecords_twirl_integrable d A a b

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The full complex Born trace is the real QIT probability because the state is positive. -/
theorem basisBorn_complex_trace (U : ↥(unitary (Matrix I I ℂ))) (ρ : QIT.State I) (x : I) :
    (basisBorn U ρ x : ℂ) = (ρ.matrix * (basisPOVM U).effects x).trace := by
  have he : (ρ.matrix * (basisPOVM U).effects x).trace =
      (U.val.conjTranspose * ρ.matrix * U.val) x x := by
    rw [basisPOVM_effect]
    calc
      _ = ((U.val.conjTranspose * ρ.matrix * U.val) * Matrix.single x x (1 : ℂ)).trace := by
        simpa only [Matrix.mul_assoc] using
          Matrix.trace_mul_comm (ρ.matrix * U.val * Matrix.single x x (1 : ℂ)) U.val.conjTranspose
      _ = _ := by rw [Matrix.trace_mul_single]; simp
  rw [he, basisBorn_diagonal]
  have h := (ρ.pos.conjTranspose_mul_mul_same U.val).diag_nonneg (i := x)
  have him := (Complex.nonneg_iff.mp h).2
  apply Complex.ext <;> simp [him]

/-- Born probabilities vary continuously on the complete basis/outcome record space. -/
theorem basisBorn_record_continuous (d : ℕ) (ρ : QIT.State (Fin d)) :
    Continuous (fun ω : CertificationGaussian.ComplexUnitary (Fin d) × Fin d => basisBorn ω.1 ρ ω.2) := by
  have he : (fun ω : CertificationGaussian.ComplexUnitary (Fin d) × Fin d => basisBorn ω.1 ρ ω.2) =
      (fun ω => Matrix.trace (CertificationGaussian.recordedProjector d ω * ρ.matrix) |>.re) := by
    funext ω
    rw [basisBorn_trace, basisPOVM_recordedProjector, Matrix.trace_mul_comm]
  rw [he]
  exact Complex.continuous_re.comp (CertificationGaussian.recordedProjector_trace_continuous d ρ.matrix)

/-- State-dependent density relative to the independent Haar-basis/uniform-outcome reference law. -/
def haarBornDensity (d : ℕ) (ρ : QIT.State (Fin d))
    (ω : CertificationGaussian.ComplexUnitary (Fin d) × Fin d) : ℝ :=
  (d : ℝ) * basisBorn ω.1 ρ ω.2

theorem haarBornDensity_nonneg (d : ℕ) (ρ : QIT.State (Fin d))
    (ω : CertificationGaussian.ComplexUnitary (Fin d) × Fin d) : 0 ≤ haarBornDensity d ρ ω :=
  mul_nonneg (Nat.cast_nonneg d) (basisBorn_nonneg ω.1 ρ ω.2)

theorem haarBornDensity_continuous (d : ℕ) (ρ : QIT.State (Fin d)) :
    Continuous (haarBornDensity d ρ) :=
  continuous_const.mul (basisBorn_record_continuous d ρ)

theorem haarBornDensity_integrable (d : ℕ) [NeZero d] (ρ : QIT.State (Fin d)) :
    Integrable (haarBornDensity d ρ) (CertificationGaussian.haarBasisRecords d) :=
  (haarBornDensity_continuous d ρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem haarBornDensity_integral (d : ℕ) [NeZero d] (ρ : QIT.State (Fin d)) :
    ∫ ω, haarBornDensity d ρ ω ∂CertificationGaussian.haarBasisRecords d = 1 := by
  have hc : Continuous (fun ω : CertificationGaussian.ComplexUnitary (Fin d) × Fin d =>
      (basisBorn ω.1 ρ ω.2 : ℂ)) := Complex.continuous_ofReal.comp (basisBorn_record_continuous d ρ)
  have h := CertificationGaussian.haarBasisRecords_scaled_integral d _ hc
  have hs (U : CertificationGaussian.ComplexUnitary (Fin d)) : (∑ k, (basisBorn U ρ k : ℂ)) = 1 := by
    exact_mod_cast basisBorn_sum U ρ
  simp only [hs] at h
  simp at h
  rw [integral_complex_ofReal] at h
  have hr : (d : ℝ) * (∫ ω, basisBorn ω.1 ρ ω.2 ∂CertificationGaussian.haarBasisRecords d) = 1 := by
    exact_mod_cast h
  simpa only [haarBornDensity, integral_const_mul] using hr

/-- The actual state-dependent Born record law; it is distinct from the reference law. -/
def haarBornRecordLaw (d : ℕ) (ρ : QIT.State (Fin d)) :
    Measure (CertificationGaussian.ComplexUnitary (Fin d) × Fin d) :=
  (CertificationGaussian.haarBasisRecords d).withDensity (fun ω => ENNReal.ofReal (haarBornDensity d ρ ω))

instance haarBornRecordLaw_probability (d : ℕ) [NeZero d] (ρ : QIT.State (Fin d)) :
    IsProbabilityMeasure (haarBornRecordLaw d ρ) where
  measure_univ := by
    rw [haarBornRecordLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (haarBornDensity_integrable d ρ)
        (Filter.Eventually.of_forall (haarBornDensity_nonneg d ρ)), haarBornDensity_integral]
    simp

/-- The actual Born-law integral is the reference-law integral weighted by d times the QIT probability. -/
theorem haarBornRecordLaw_integral (d : ℕ) (ρ : QIT.State (Fin d))
    (f : CertificationGaussian.ComplexUnitary (Fin d) × Fin d → ℂ) :
    ∫ ω, f ω ∂haarBornRecordLaw d ρ =
      ∫ ω, haarBornDensity d ρ ω • f ω ∂CertificationGaussian.haarBasisRecords d := by
  rw [haarBornRecordLaw, integral_withDensity_eq_integral_toReal_smul
    (haarBornDensity_continuous d ρ).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (haarBornDensity_nonneg d ρ _)]

theorem haarBornRecordLaw_projector_integrable (d : ℕ) [NeZero d]
    (ρ : QIT.State (Fin d)) (a b : Fin d) :
    Integrable (fun ω => (basisPOVM ω.1).effects ω.2 a b) (haarBornRecordLaw d ρ) := by
  simp_rw [basisPOVM_recordedProjector]
  exact (CertificationGaussian.recordedProjector_entry_continuous d a b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Under the real Born record law, the mean recorded effect is exactly T_s(rho). -/
theorem haarBornRecordLaw_projector_mean (d : ℕ) [NeZero d]
    (ρ : QIT.State (Fin d)) (a b : Fin d) :
    ∫ ω, (basisPOVM ω.1).effects ω.2 a b ∂haarBornRecordLaw d ρ =
      (ρ.matrix a b + if a=b then 1 else 0) / ((d : ℂ)+1) := by
  rw [haarBornRecordLaw_integral]
  calc
    _ = (d : ℂ) * ∫ ω, (basisPOVM ω.1).effects ω.2 a b * (basisBorn ω.1 ρ ω.2 : ℂ)
        ∂CertificationGaussian.haarBasisRecords d := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [haarBornDensity, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_natCast]
      ring
    _ = _ := by
      have he (ω : CertificationGaussian.ComplexUnitary (Fin d) × Fin d) :
          (basisBorn ω.1 ρ ω.2 : ℂ) = ((basisPOVM ω.1).effects ω.2 * ρ.matrix).trace := by
        rw [basisBorn_complex_trace, Matrix.trace_mul_comm]
      simp_rw [he]
      simpa only [ρ.trace_eq_one] using (qit_haar_record_twirl d ρ.matrix a b).1

end LocalCertification.Quantum
