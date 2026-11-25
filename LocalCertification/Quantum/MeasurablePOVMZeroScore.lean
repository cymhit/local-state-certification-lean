import LocalCertification.Quantum.MeasurablePOVMFrameScore

/-! The pure-minus-uniform branch uses the literal zero-radius kernel.
It is independent of the degree-zero dual certificate, whose residual starts at radius one. -/
set_option autoImplicit false
open MeasureTheory Matrix Metric Set
open scoped ENNReal ComplexOrder
noncomputable section
namespace LocalCertification.Quantum
private theorem zeroScore_spherePureVector_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) (B : Matrix I I ℂ) :
    ((spherePureVector ψ).state.matrix * B).trace =
      CertificationGaussian.sphereQuadraticForm B ψ := by
  rw [Matrix.trace_mul_comm]
  change (B * CertificationGaussian.vectorRankOne (ψ : EuclideanSpace ℂ I) ψ).trace = _
  exact CertificationGaussian.vectorRankOne_trace_pairing B ψ

variable {d n : ℕ} [NeZero d] {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- The actual refined pure-minus-uniform squared density is the zero-radius frame score. -/
theorem pure_refined_difference_sq_eq_zeroFrame (hd : 2 ≤ d)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (∫ s, (MeasurablePOVM.productRefinedBornDensity M (spherePureVector ψ).state s -
      MeasurablePOVM.productRefinedBornDensity M (quditMaximallyMixed d n) s)^2
      ∂MeasurablePOVM.productRefinementReference M) =
      CertificationGaussian.gaussianFrameSphereScore
        ((CertificationGaussian.signedProductMatrixFrame {0} (fun _ => 1)
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
  have h := CertificationGaussian.productFrame_sphereScore_eq_integral
    (fun i => (M i).refinementReference) u
    (fun i => (M i).refinementUnitVector_measurable)
    (fun i p => (M i).refinementUnitVector_norm p.1 p.2)
    (by simpa using hd) {0} (fun _ => 1)
    (by intro k hk; simpa only [Finset.mem_singleton.mp hk] using Nat.zero_le (Fintype.card (Fin n)))
    (by simp) ψ
  rw [hf] at h
  rw [h]
  apply integral_congr_ae
  refine ae_of_all _ (fun s => ?_)
  dsimp only
  have hK : CertificationGaussian.productFrameKernel u {0} (fun _ => 1) s =
      MeasurablePOVM.productRefinementProjector M s := by
    change CertificationGaussian.cardinalityProjectorKernel _ _ _ = _
    rw [CertificationGaussian.cardinalityProjectorKernel_zero]
    simp only [Complex.ofReal_one, one_smul]
    change tensorMatrix _ = tensorMatrix _
    exact congrArg tensorMatrix
      (funext fun i =>
        congrFun (he i) (s i))
  have hm : MeasurablePOVM.productRefinedBornDensity M (quditMaximallyMixed d n) s = 1 := by
    have hstate : quditMaximallyMixed d n = QIT.State.maximallyMixed (Fin n → Fin d) := rfl
    rw [hstate]
    exact MeasurablePOVM.productRefinedBornDensity_maximallyMixed M s
  rw [hK, hm, MeasurablePOVM.productRefinedBornDensity_eq, zeroScore_spherePureVector_pairing]

/-- Forgetting the refinement labels contracts the actual original-reference distance. -/
theorem pure_product_referenceL2_sq_le_zeroFrame (hd : 2 ≤ d)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (∫ s, ((MeasurablePOVM.product M).bornDensity (spherePureVector ψ).state s -
      (MeasurablePOVM.product M).bornDensity (quditMaximallyMixed d n) s)^2
      ∂(MeasurablePOVM.product M).traceReference) ≤
      CertificationGaussian.gaussianFrameSphereScore
        ((CertificationGaussian.signedProductMatrixFrame {0} (fun _ => 1)
          (fun i => (M i).refinementComplexFrame)).restrictScalars ℝ) ψ := by
  exact (MeasurablePOVM.product_referenceL2_sq_le_localRefinement M
    (spherePureVector ψ).state (quditMaximallyMixed d n)).trans_eq
      (pure_refined_difference_sq_eq_zeroFrame hd ψ M)

/-- The same fixed zero-radius frame event controls every arbitrary measurable product POVM. -/
theorem pure_product_referenceL2_sq_le_of_frameFamily (hd : 2 ≤ d)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (H : ℝ)
    (hcommon : ∀ T ∈ CertificationGaussian.signedProductFrameFamily
      (S := Fin n) (I := Fin d) {0} (fun _ => 1),
      CertificationGaussian.gaussianFrameSphereScore T ψ ≤ H)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (∫ s, ((MeasurablePOVM.product M).bornDensity (spherePureVector ψ).state s -
      (MeasurablePOVM.product M).bornDensity (quditMaximallyMixed d n) s)^2
      ∂(MeasurablePOVM.product M).traceReference) ≤ H :=
  (pure_product_referenceL2_sq_le_zeroFrame hd ψ M).trans
    (hcommon _ (MeasurablePOVM.productRefinementComplexFrame_mem_family M _ _))

end LocalCertification.Quantum
