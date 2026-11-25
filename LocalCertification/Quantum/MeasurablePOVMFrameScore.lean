import LocalCertification.Quantum.MeasurableDualInformation
import LocalCertification.Quantum.HaarWeylOverlap
import LocalCertification.Quantum.MeasurablePOVMFrameCanonical
import CertificationGaussian.ProductFrameGaussianBridge

/-! The literal QIT hard-state residual and the sphere quadratic observable.
The same target amplitudes, complement kernel, and product refinement law occur
on both sides. The product-frame operator identification is added from the
independently verified physical-frame bridge. -/

open MeasureTheory Matrix Metric Set LocalCertification.Extremal
open scoped ENNReal ComplexOrder
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

private theorem spherePureVector_matrix_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) (B : Matrix I I ℂ) :
    ((spherePureVector ψ).state.matrix * B).trace =
      CertificationGaussian.sphereQuadraticForm B ψ := by
  rw [Matrix.trace_mul_comm]
  change (B * CertificationGaussian.vectorRankOne (ψ : EuclideanSpace ℂ I) ψ).trace = _
  exact CertificationGaussian.vectorRankOne_trace_pairing B ψ

variable {d n r : ℕ} [NeZero d]

private theorem spherePureVector_centered_pairing
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (B : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ)
    (hB : B.trace = 1) :
    (d : ℝ)^n * (((spherePureVector ψ).state.matrix - (quditMaximallyMixed d n).matrix) * B).trace.re =
      (d : ℝ)^n * (CertificationGaussian.sphereQuadraticForm B ψ).re - 1 := by
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, spherePureVector_matrix_pairing,
    quditMaximallyMixed_matrix, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hB]
  simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
  rw [mul_sub, mul_inv_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.mpr (NeZero.ne d)))]

/-- The original fixed-dual residual is exactly the sphere integral for the same physical kernel. -/
theorem dualResidualQuadratic_eq_sphereIntegral
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r) (hN : c.maxNode ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    dualResidualQuadratic c (spherePureVector ψ) M =
      ∫ s, ((d : ℝ)^n *
        (CertificationGaussian.sphereQuadraticForm
          (CertificationGaussian.cardinalityProjectorKernel
            (fun i => (M i).refinementProjector (s i).1 (s i).2)
            (residualRadii c) (residualWeight d c)) ψ).re - 1)^2
        ∂MeasurablePOVM.productRefinementReference M := by
  change (d : ℝ)^(2*n) *
    (∫ s, ((((spherePureVector ψ).state.matrix - (quditMaximallyMixed d n).matrix) *
      CertificationGaussian.cardinalityProjectorKernel
        (fun i => (M i).refinementProjector (s i).1 (s i).2)
        (residualRadii c) (residualWeight d c)).trace.re)^2
      ∂MeasurablePOVM.productRefinementReference M) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ (fun s => ?_)
  dsimp only
  have hp : (d : ℝ)^(2*n) = ((d : ℝ)^n)^2 := by rw [← pow_mul, Nat.mul_comm]
  rw [hp, ← mul_pow, spherePureVector_centered_pairing ψ _
    (dualComplementKernel_trace hd c hN _
      (fun i => (M i).refinementProjector_trace (s i).1 (s i).2))]

/-- The literal residual uses the actual local refinement frames, in the fixed family. -/
theorem dualResidualQuadratic_eq_productFrameSphereScore
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r) (hN : c.maxNode ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    dualResidualQuadratic c (spherePureVector ψ) M =
      CertificationGaussian.gaussianFrameSphereScore
        ((CertificationGaussian.signedProductMatrixFrame (residualRadii c) (residualWeight d c)
          (fun i => (M i).refinementComplexFrame)).restrictScalars ℝ) ψ := by
  let u (i : Fin n) (p : Ω i × Fin d) := (M i).refinementUnitVector p.1 p.2
  have he (i : Fin n) :
      (fun p : Ω i × Fin d => CertificationGaussian.vectorRankOne (u i p) (u i p)) =
        (fun p => (M i).refinementProjector p.1 p.2) := by
    funext p
    exact ((M i).refinementProjector_eq_vectorRankOne p.1 p.2).symm
  have hf : (fun i => CertificationGaussian.integralComplexMatrixFrame
      (M i).refinementReference (fun p => CertificationGaussian.vectorRankOne (u i p) (u i p))) =
        (fun i => (M i).refinementComplexFrame) := by
    funext i
    exact congrArg (CertificationGaussian.integralComplexMatrixFrame (M i).refinementReference) (he i)
  have hJ : ∀ k ∈ residualRadii c, k ≤ Fintype.card (Fin n) := by
    intro k hk
    exact (Finset.mem_Icc.mp hk).2.trans (by simpa using hN)
  have h := CertificationGaussian.productFrame_sphereScore_eq_integral
    (fun i => (M i).refinementReference) u
    (fun i => (M i).refinementUnitVector_measurable)
    (fun i p => (M i).refinementUnitVector_norm p.1 p.2)
    (by simpa using hd) (residualRadii c) (residualWeight d c) hJ
    (residualWeight_mass d (by omega) c) ψ
  rw [hf] at h
  rw [dualResidualQuadratic_eq_sphereIntegral hd c hN ψ M, h]
  apply integral_congr_ae
  refine ae_of_all _ (fun s => ?_)
  dsimp only
  have hK : CertificationGaussian.productFrameKernel u (residualRadii c) (residualWeight d c) s =
      CertificationGaussian.cardinalityProjectorKernel
        (fun i => (M i).refinementProjector (s i).1 (s i).2)
        (residualRadii c) (residualWeight d c) := by
    exact congrArg
      (fun projectors => CertificationGaussian.cardinalityProjectorKernel projectors
        (residualRadii c) (residualWeight d c))
      (funext fun i => congrFun (he i) (s i))
  rw [hK]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- A single event on the fixed frame family controls every measurable local POVM. -/
theorem dualResidualQuadratic_le_of_frameFamily
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r) (hN : c.maxNode ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (H : ℝ)
    (hcommon : ∀ T ∈ CertificationGaussian.signedProductFrameFamily
      (S := Fin n) (I := Fin d) (residualRadii c) (residualWeight d c),
      CertificationGaussian.gaussianFrameSphereScore T ψ ≤ H)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    dualResidualQuadratic c (spherePureVector ψ) M ≤ H := by
  rw [dualResidualQuadratic_eq_productFrameSphereScore hd c hN ψ M]
  exact hcommon _ (MeasurablePOVM.productRefinementComplexFrame_mem_family M _ _)

end LocalCertification.Quantum
