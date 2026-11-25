import CertificationGaussian.ReadoutMomentOperators

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]

/-- The actual first-moment matrix for the original cardinality kernel. -/
def cardinalityReadoutMean (d : ℕ) (μ : Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (r : ℕ) (lam : ℕ → ℝ)
    (qscale : ℝ) (z : (S → Fin d) → ℂ) : Matrix (S → Fin d) (S → Fin d) ℂ :=
  readoutMeanOperator (Measure.pi (fun _ : S => μ)) ((d:ℝ)^(Fintype.card S))
    (productRecordedProjector d record) (cardinalityReadoutKernel d record r lam)
    (cardinalityReadoutTraceScale d (Fintype.card S) r lam) qscale z

/-- The actual full second-moment matrix, with the same record, kernel and centered score. -/
def cardinalityReadoutSecond (d : ℕ) (μ : Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (r : ℕ) (lam : ℕ → ℝ)
    (qscale : ℝ) (z : (S → Fin d) → ℂ) : Matrix (S → Fin d) (S → Fin d) ℂ :=
  readoutSecondOperator (Measure.pi (fun _ : S => μ)) ((d:ℝ)^(Fintype.card S))
    (productRecordedProjector d record) (cardinalityReadoutKernel d record r lam)
    (cardinalityReadoutTraceScale d (Fintype.card S) r lam) qscale z

/-- The actual auxiliary quadratic matrix, with nu equal to the proved trace of H squared. -/
def cardinalityReadoutAuxiliary (d : ℕ) (μ : Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (r : ℕ) (lam : ℕ → ℝ)
    (qscale : ℝ) (z : (S → Fin d) → ℂ) : Matrix (S → Fin d) (S → Fin d) ℂ :=
  readoutAuxiliaryOperator (Measure.pi (fun _ : S => μ)) ((d:ℝ)^(Fintype.card S))
    (productRecordedProjector d record) (cardinalityReadoutKernel d record r lam)
    (cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => (lam j)^2)) qscale z

section GeneralRecord
variable [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
variable (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
variable (hmean : ∀ a b : Fin d,(d:ℂ)*(∫ ω,recordedProjector d (record ω) a b∂μ)=
  (1:Matrix (Fin d) (Fin d) ℂ) a b)

include hr hmean

/-- All trace and full-product normalization inputs are concretely discharged for the original cardinality kernel. -/
theorem cardinalityReadoutSecond_gaussian_identity (r : ℕ) (lam : ℕ → ℝ)
    (z : (S → Fin d) → ℂ) :
    cardinalityReadoutSecond d μ record r lam 1 z =
      cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => (lam j)^2) • (1:Matrix (S → Fin d) (S → Fin d) ℂ)+
      cardinalityReadoutAuxiliary d μ record r lam 1 z+cardinalityReadoutRemainder d μ record r lam z :=
  readoutSecondOperator_gaussian_identity (Measure.pi (fun _ : S => μ)) _ _ _ _ _
    (productRecordedProjector_continuous d record hr) (finiteComplementKernel_continuous d record hr _ _)
    (cardinalityReadoutKernel_trace d record r lam) (cardinalityReadoutKernel_trace_sq d record r lam)
    (productRecordedProjector_mean d μ record hr hmean) z

/-- The same actual full moments obey the exact direction/radius identity, not an asymptotic surrogate. -/
theorem cardinalityReadoutSecond_direction_identity (r : ℕ) (lam : ℕ → ℝ)
    (z : (S → Fin d) → ℂ) (hz : (WithLp.toLp 2 z : EuclideanSpace ℂ (S → Fin d))≠0)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ (S → Fin d)) 1) :
    let D := (d:ℝ)^(Fintype.card S)
    let h := cardinalityReadoutTraceScale d (Fintype.card S) r lam
    let nu := cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => (lam j)^2)
    let ψ : (S → Fin d) → ℂ := (sphereDirection e₀ (WithLp.toLp 2 z) : EuclideanSpace ℂ (S → Fin d))
    let a := readoutRadialAlpha D z
    cardinalityReadoutSecond d μ record r lam D ψ =
      nu • (1:Matrix (S → Fin d) (S → Fin d) ℂ)+a • cardinalityReadoutAuxiliary d μ record r lam D ψ+
      a^2 • cardinalityReadoutRemainder d μ record r lam z+
      (2*(a-1)*h) • cardinalityReadoutMean d μ record r lam D ψ-
      ((a-1)^2*(nu+h^2)) • (1:Matrix (S → Fin d) (S → Fin d) ℂ) :=
  readoutSecondOperator_direction_identity (Measure.pi (fun _ : S => μ)) _ _ _ _ _
    (productRecordedProjector_continuous d record hr) (finiteComplementKernel_continuous d record hr _ _)
    (cardinalityReadoutKernel_trace d record r lam) (cardinalityReadoutKernel_trace_sq d record r lam)
    (productRecordedProjector_mean d μ record hr hmean) z hz e₀
end GeneralRecord

/-- Full-Haar actual Gaussian second moment, without supplied trace/normalization hypotheses. -/
theorem cardinalityHaar_second_gaussian_identity (d r : ℕ) [NeZero d] (lam : ℕ → ℝ)
    (z : (S → Fin d) → ℂ) :
    cardinalityReadoutSecond d (haarBasisRecords d) id r lam 1 z =
      cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => (lam j)^2) • (1:Matrix (S → Fin d) (S → Fin d) ℂ)+
      cardinalityReadoutAuxiliary d (haarBasisRecords d) id r lam 1 z+
      cardinalityReadoutRemainder d (haarBasisRecords d) id r lam z :=
  cardinalityReadoutSecond_gaussian_identity d (haarBasisRecords d) id continuous_id
    (haarBasisRecords_projector_mean d) r lam z

/-- The genuine finite three-Pauli-basis Gaussian second identity. -/
theorem cardinalityPauli_second_gaussian_identity (r : ℕ) (lam : ℕ → ℝ)
    (z : (S → Fin 2) → ℂ) :
    cardinalityReadoutSecond 2 pauliBasisRecords pauliFullRecord r lam 1 z =
      cardinalityReadoutTraceScale 2 (Fintype.card S) r (fun j => (lam j)^2) • (1:Matrix (S → Fin 2) (S → Fin 2) ℂ)+
      cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord r lam 1 z+
      cardinalityReadoutRemainder 2 pauliBasisRecords pauliFullRecord r lam z :=
  cardinalityReadoutSecond_gaussian_identity 2 pauliBasisRecords pauliFullRecord continuous_of_discreteTopology
    pauliBasisRecords_projector_mean r lam z

/-- The actual complete-record radial full-second-moment identity, with every trace and normalization premise proved. -/
theorem cardinalityHaar_second_direction_identity (d r : ℕ) [NeZero d] (lam : ℕ → ℝ)
    (z : (S → Fin d) → ℂ) (hz : (WithLp.toLp 2 z : EuclideanSpace ℂ (S → Fin d))≠0)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ (S → Fin d)) 1) :
    let D := (d:ℝ)^(Fintype.card S)
    let h := cardinalityReadoutTraceScale d (Fintype.card S) r lam
    let nu := cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => (lam j)^2)
    let ψ : (S → Fin d) → ℂ := (sphereDirection e₀ (WithLp.toLp 2 z) : EuclideanSpace ℂ (S → Fin d))
    let a := readoutRadialAlpha D z
    cardinalityReadoutSecond d (haarBasisRecords d) id r lam D ψ =
      nu • (1:Matrix (S → Fin d) (S → Fin d) ℂ)+a • cardinalityReadoutAuxiliary d (haarBasisRecords d) id r lam D ψ+
      a^2 • cardinalityReadoutRemainder d (haarBasisRecords d) id r lam z+
      (2*(a-1)*h) • cardinalityReadoutMean d (haarBasisRecords d) id r lam D ψ-
      ((a-1)^2*(nu+h^2)) • (1:Matrix (S → Fin d) (S → Fin d) ℂ) :=
  cardinalityReadoutSecond_direction_identity d (haarBasisRecords d) id continuous_id
    (haarBasisRecords_projector_mean d) r lam z hz e₀

/-- The actual complete-record radial full-second-moment identity, with every trace and normalization premise proved. -/
theorem cardinalityPauli_second_direction_identity (r : ℕ) (lam : ℕ → ℝ)
    (z : (S → Fin 2) → ℂ) (hz : (WithLp.toLp 2 z : EuclideanSpace ℂ (S → Fin 2))≠0)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ (S → Fin 2)) 1) :
    let D := (2:ℝ)^(Fintype.card S)
    let h := cardinalityReadoutTraceScale 2 (Fintype.card S) r lam
    let nu := cardinalityReadoutTraceScale 2 (Fintype.card S) r (fun j => (lam j)^2)
    let ψ : (S → Fin 2) → ℂ := (sphereDirection e₀ (WithLp.toLp 2 z) : EuclideanSpace ℂ (S → Fin 2))
    let a := readoutRadialAlpha D z
    cardinalityReadoutSecond 2 pauliBasisRecords pauliFullRecord r lam D ψ =
      nu • (1:Matrix (S → Fin 2) (S → Fin 2) ℂ)+a • cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord r lam D ψ+
      a^2 • cardinalityReadoutRemainder 2 pauliBasisRecords pauliFullRecord r lam z+
      (2*(a-1)*h) • cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam D ψ-
      ((a-1)^2*(nu+h^2)) • (1:Matrix (S → Fin 2) (S → Fin 2) ℂ) :=
  cardinalityReadoutSecond_direction_identity 2 pauliBasisRecords pauliFullRecord continuous_of_discreteTopology
    pauliBasisRecords_projector_mean r lam z hz e₀

end CertificationGaussian
