import CertificationGaussian.CardinalityReadoutMoments
import CertificationGaussian.Consumers.ReadoutRemainderTail

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- The Haar Gaussian second moment splits into the scalar, auxiliary and remainder operators. -/
theorem paper_haar_second_identity (d n r : ℕ) [NeZero d] (lam : ℕ → ℝ)
    (z : QuditIndex d n → ℂ) :
    cardinalityReadoutSecond d (haarBasisRecords d) id r lam 1 z =
      cardinalityReadoutTraceScale d n r (fun j => (lam j)^2) • (1:Matrix (QuditIndex d n) (QuditIndex d n) ℂ)+
      cardinalityReadoutAuxiliary d (haarBasisRecords d) id r lam 1 z+
      cardinalityReadoutRemainder d (haarBasisRecords d) id r lam z := by
  simpa only [Fintype.card_fin] using cardinalityHaar_second_gaussian_identity d r lam z

/-- Five-term matrix identity for the full Pauli second-moment operator at the normalized target. -/
theorem paper_pauli_second_direction (n r : ℕ) (lam : ℕ → ℝ)
    (z : QuditIndex 2 n → ℂ) (hz : (WithLp.toLp 2 z : EuclideanSpace ℂ (QuditIndex 2 n))≠0)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1) :
    let D := (2:ℝ)^n
    let h := cardinalityReadoutTraceScale 2 n r lam
    let nu := cardinalityReadoutTraceScale 2 n r (fun j => (lam j)^2)
    let ψ : QuditIndex 2 n → ℂ := (sphereDirection e₀ (WithLp.toLp 2 z) : EuclideanSpace ℂ (QuditIndex 2 n))
    let a := readoutRadialAlpha D z
    cardinalityReadoutSecond 2 pauliBasisRecords pauliFullRecord r lam D ψ =
      nu • (1:Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ)+a • cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord r lam D ψ+
      a^2 • cardinalityReadoutRemainder 2 pauliBasisRecords pauliFullRecord r lam z+
      (2*(a-1)*h) • cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam D ψ-
      ((a-1)^2*(nu+h^2)) • (1:Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ) := by
  simpa only [Fintype.card_fin] using cardinalityPauli_second_direction_identity r lam z hz e₀

/-- Exact signed trace scale, evaluated separately from the actual large matrix type. -/
theorem signedPaperCoefficients_traceScale :
    cardinalityReadoutTraceScale 2 16 2 signedPaperCoefficients=(-31:ℝ) := by
  norm_num [cardinalityReadoutTraceScale,signedPaperCoefficients,Fin.sum_univ_succ]

/-- Exact squared trace scale for the same signed coefficient sequence. -/
theorem signedPaperCoefficients_squareScale :
    cardinalityReadoutTraceScale 2 16 2 (fun j => (signedPaperCoefficients j)^2)=(65:ℝ) := by
  norm_num [cardinalityReadoutTraceScale,signedPaperCoefficients,Fin.sum_univ_succ]

/-- A signed kernel retains its negative trace and positive squared trace on every actual record. -/
theorem actual_signed_kernel_traces (ω : Fin 16 → PauliRecord) :
    Matrix.trace (cardinalityReadoutKernel 2 pauliFullRecord 2 signedPaperCoefficients ω)=(-31:ℂ) ∧
    Matrix.trace ((cardinalityReadoutKernel 2 pauliFullRecord 2 signedPaperCoefficients ω)^2)=(65:ℂ) := by
  constructor
  · simpa only [Fintype.card_fin,signedPaperCoefficients_traceScale,Complex.ofReal_neg,Complex.ofReal_ofNat] using
      cardinalityReadoutKernel_trace 2 pauliFullRecord 2 signedPaperCoefficients ω
  · simpa only [Fintype.card_fin,signedPaperCoefficients_squareScale,Complex.ofReal_ofNat] using
      cardinalityReadoutKernel_trace_sq 2 pauliFullRecord 2 signedPaperCoefficients ω

/-- Empty physical sites give one-dimensional tensor coordinates, even for d=0 in this algebraic statement. -/
theorem actual_empty_sites_kernel_trace (a : ℝ)
    (ω : Fin 0 → ComplexUnitary (Fin 0) × Fin 0) :
    Matrix.trace (cardinalityReadoutKernel 0 id 0 (fun _ => a) ω)=(a:ℂ) ∧
    Matrix.trace ((cardinalityReadoutKernel 0 id 0 (fun _ => a) ω)^2)=((a^2:ℝ):ℂ) := by
  rw [cardinalityReadoutKernel_trace,cardinalityReadoutKernel_trace_sq]
  simp [cardinalityReadoutTraceScale]

/-- The zero-vector radial scalar is defined, while the actual direction theorem correctly requires nonzero input. -/
theorem actual_zero_radial_scalar (D : ℝ) :
    readoutRadialAlpha D (0 : Fin 1 → ℂ)=0 := by
  simp [readoutRadialAlpha]

end CertificationGaussian.Consumers
