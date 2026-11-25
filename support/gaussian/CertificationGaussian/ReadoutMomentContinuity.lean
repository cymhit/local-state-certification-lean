import CertificationGaussian.ReadoutFullSecondControl
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

section CompactRecord
variable {Ω I : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [SecondCountableTopology Ω] [Fintype I] [DecidableEq I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [SecondCountableTopology Ω] in
/-- The actual full second-moment integral is continuous in its vector; compact-record continuity supplies domination. -/
theorem readoutSecondOperator_vector_continuous (D h qscale : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) :
    Continuous (fun z : EuclideanSpace ℂ I => readoutSecondOperator μ D P H h qscale z.ofLp) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  have he (z : EuclideanSpace ℂ I) :
      readoutSecondOperator μ D P H h qscale z.ofLp a b=
        D • ∫ ω,((qscale:ℂ)*sphereQuadraticForm (H ω) z-(h:ℂ))^2*P ω a b∂μ := by
    rw [readoutSecondOperator,Matrix.smul_apply,
      matrix_entry_integral μ _ (by unfold readoutCenteredScore sphereQuadraticForm; fun_prop)]
    rfl
  simp_rw [he]
  have hf : Continuous (fun p : EuclideanSpace ℂ I × Ω =>
      ((qscale:ℂ)*sphereQuadraticForm (H p.2) p.1-(h:ℂ))^2*P p.2 a b) := by
    unfold sphereQuadraticForm
    fun_prop
  have hi := continuous_parametric_integral_of_continuous (μ:=μ)
    (f:=fun (z : EuclideanSpace ℂ I) (ω : Ω) =>
      ((qscale:ℂ)*sphereQuadraticForm (H ω) z-(h:ℂ))^2*P ω a b) hf isCompact_univ
  simp only [Complex.real_smul]
  convert continuous_const.mul hi (f:=fun _ => (D:ℂ)) using 1
  funext z
  simp only [Pi.mul_apply,setIntegral_univ]

omit [SecondCountableTopology Ω] in
/-- The true auxiliary S integral is continuous in its vector under the same actual reference law. -/
theorem readoutAuxiliaryOperator_vector_continuous (D nu qscale : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) :
    Continuous (fun z : EuclideanSpace ℂ I => readoutAuxiliaryOperator μ D P H nu qscale z.ofLp) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  have he (z : EuclideanSpace ℂ I) :
      readoutAuxiliaryOperator μ D P H nu qscale z.ofLp a b=
        D • ∫ ω,(2*((qscale:ℂ)*sphereQuadraticForm ((H ω)^2) z-(nu:ℂ)))*P ω a b∂μ := by
    rw [readoutAuxiliaryOperator,Matrix.smul_apply,
      matrix_entry_integral μ _ (by unfold sphereQuadraticForm; fun_prop)]
    rfl
  simp_rw [he]
  have hf : Continuous (fun p : EuclideanSpace ℂ I × Ω =>
      (2*((qscale:ℂ)*sphereQuadraticForm ((H p.2)^2) p.1-(nu:ℂ)))*P p.2 a b) := by
    unfold sphereQuadraticForm
    fun_prop
  have hi := continuous_parametric_integral_of_continuous (μ:=μ)
    (f:=fun (z : EuclideanSpace ℂ I) (ω : Ω) =>
      (2*((qscale:ℂ)*sphereQuadraticForm ((H ω)^2) z-(nu:ℂ)))*P ω a b) hf isCompact_univ
  simp only [Complex.real_smul]
  convert continuous_const.mul hi (f:=fun _ => (D:ℂ)) using 1
  funext z
  simp only [Pi.mul_apply,setIntegral_univ]

end CompactRecord

/-- The actual cardinality full-second error has a continuous Euclidean operator-norm function. -/
theorem cardinalityReadoutSecondError_continuous {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (d n r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record) (lam : ℕ → ℝ) :
    Continuous (cardinalityReadoutSecondError d n r μ record lam) := by
  have hP := productRecordedProjector_continuous (S:=Fin n) d record hr
  have hH := finiteComplementKernel_continuous (S:=Fin n) d record hr
    (fun k : CardinalityComplementIndex (Fin n) r => cardinalityComplementSet k)
    (fun k => lam k.1)
  have hm := readoutSecondOperator_vector_continuous (Measure.pi (fun _ : Fin n => μ))
    ((d:ℝ)^n) (cardinalityReadoutTraceScale d n r lam) ((d:ℝ)^n)
    (productRecordedProjector d record) (cardinalityReadoutKernel d record r lam) hP hH
  have hs := readoutAuxiliaryOperator_vector_continuous (Measure.pi (fun _ : Fin n => μ))
    ((d:ℝ)^n) (cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)) ((d:ℝ)^n)
    (productRecordedProjector d record) (cardinalityReadoutKernel d record r lam) hP hH
  unfold cardinalityReadoutSecondError cardinalityReadoutSecond cardinalityReadoutAuxiliary
  simp only [Fintype.card_fin,Matrix.l2_opNorm_toEuclideanCLM]
  exact ((hm.sub continuous_const).sub hs).norm

end CertificationGaussian
