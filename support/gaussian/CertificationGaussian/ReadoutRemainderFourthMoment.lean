import CertificationGaussian.ReadoutRemainderModel

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

section CompactRecord
variable {Ω I : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [SecondCountableTopology Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
local instance : IsProbabilityMeasure (pairedGaussian I) := by
  unfold pairedGaussian
  infer_instance

/-- The fourth trace of the actual matrix integral is the actual four-record integral at every z. -/
theorem normalReadoutRemainder_trace_fourth (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) (z : I → ℂ) :
    Matrix.trace ((normalReadoutRemainder μ D P H z)^4) =
      (D:ℂ)^4*∫ x,Matrix.trace (P x.1*P x.2.1*P x.2.2.1*P x.2.2.2)*
        ∏ b : Fin 4,complexGaussianNormalMatrix (H (fourRecordAt x b)) (H (fourRecordAt x b)) z
          ∂fourReadoutLaw μ := by
  unfold normalReadoutRemainder
  rw [smul_pow,Matrix.trace_smul]
  simp only [Complex.real_smul,Complex.ofReal_pow]
  rw [← fourReadout_matrix_product_integral μ _ (normalReadoutRemainder_integrand_continuous P H hP hH z)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp [smul_smul,Matrix.trace_smul,smul_eq_mul,
    fourRecordAt,Fin.prod_univ_succ]
  ring

/-- The true Gaussian fourth trace is absolutely integrable; joint integrability is proved by finite normal-polynomial expansion. -/
theorem normalReadoutRemainder_trace_fourth_integrable (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) :
    Integrable (fun z => Matrix.trace ((normalReadoutRemainder μ D P H (complexCoordinate z))^4))
      (pairedGaussian I) := by
  have hj := recordGaussian_four_blocks_integrable (fourReadoutLaw μ)
    (fun (t : Fin 4 × Fin 2) x => H (fourRecordAt x t.1)) (by intro t; fun_prop)
    (fun x => Matrix.trace (P x.1*P x.2.1*P x.2.2.1*P x.2.2.2)) (by fun_prop)
  simp_rw [funext (fun z => normalReadoutRemainder_trace_fourth μ D P H hP hH (complexCoordinate z))]
  exact hj.integral_prod_right.const_mul _

/-- The actual Z fourth moment equals the original readout-outer/Gaussian-inner formula by proved absolute Fubini. -/
theorem normalReadoutRemainder_trace_fourth_expectation (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) :
    (∫ z,Matrix.trace ((normalReadoutRemainder μ D P H (complexCoordinate z))^4) ∂pairedGaussian I) =
      (D:ℂ)^4*∫ x,Matrix.trace (P x.1*P x.2.1*P x.2.2.1*P x.2.2.2)*
        (∫ z,∏ b : Fin 4,complexGaussianNormalMatrix (H (fourRecordAt x b))
          (H (fourRecordAt x b)) (complexCoordinate z) ∂pairedGaussian I) ∂fourReadoutLaw μ := by
  have hs := recordGaussian_four_blocks_swap (fourReadoutLaw μ)
    (fun (t : Fin 4 × Fin 2) x => H (fourRecordAt x t.1)) (by intro t; fun_prop)
    (fun x => Matrix.trace (P x.1*P x.2.1*P x.2.2.1*P x.2.2.2)) (by fun_prop)
  simp_rw [normalReadoutRemainder_trace_fourth μ D P H hP hH]
  rw [integral_const_mul]
  rw [← hs]
  simp_rw [integral_const_mul]

end CompactRecord

section ProductRecord
variable {S K Ω : Type*} [Fintype S] [DecidableEq S] [Fintype K]
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω]

/-- True finite-complement Z has a finite Gaussian fourth trace moment under the original paired-coordinate model. -/
theorem finiteComplementRemainder_fourth_integrable (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) :
    Integrable (fun z => Matrix.trace ((finiteComplementRemainder d μ r A c (complexCoordinate z))^4))
      (pairedGaussian (S → Fin d)) :=
  normalReadoutRemainder_trace_fourth_integrable _ _ _ _
    (productRecordedProjector_continuous d r hr) (finiteComplementKernel_continuous d r hr A c)

/-- The actual finite-complement matrix Z and the already bounded actual Gaussian/readout contraction are identical. -/
theorem finiteComplementRemainder_fourth_expectation (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) :
    (∫ z,Matrix.trace ((finiteComplementRemainder d μ r A c (complexCoordinate z))^4)
      ∂pairedGaussian (S → Fin d)) =
      ((d:ℂ)^(Fintype.card S))^4*
        (∫ x,finiteComplementGaussianFourthIntegrand d r A c x
          ∂fourReadoutLaw (Measure.pi (fun _ : S => μ))) := by
  have h := normalReadoutRemainder_trace_fourth_expectation
    (Measure.pi (fun _ : S => μ)) ((d:ℝ)^(Fintype.card S))
    (productRecordedProjector d r) (finiteComplementKernel d r A c)
    (productRecordedProjector_continuous d r hr) (finiteComplementKernel_continuous d r hr A c)
  simpa only [finiteComplementRemainder,finiteComplementGaussianFourthIntegrand,
    Complex.ofReal_pow,Complex.ofReal_natCast] using h

end ProductRecord
end CertificationGaussian
