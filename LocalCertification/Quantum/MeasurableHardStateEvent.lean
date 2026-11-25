import LocalCertification.Quantum.MeasurablePOVMFrameScore
import LocalCertification.Quantum.MeasurableProductCalibration
import LocalCertification.Quantum.CommonHaarEvent
import CertificationGaussian.MeasurableFrameContinuity

/-! A canonical compact target event for all measurable product measurements.
Only the original finite shell overlaps and the fixed all-frame event are used.
The calibrated states remain fixed before any outcome space or measurement. -/
set_option autoImplicit false
open LocalCertification.Extremal MeasureTheory InformationTheory Matrix Metric Set
open scoped ENNReal ComplexOrder
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

/-- The fixed frame family is independent of the local measurable outcome spaces. -/
def measurableDualSphereGoodEvent (hd : 2 ≤ d) (r : ℕ)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) :
    Set (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :=
  {ψ | (∀ i : Fin (r+1), pureTargetFidelity (spherePureVector ψ)
      (pureTargetShell hd (spherePureVector ψ) ((quditDualCertificate hd r).node i)
        (((quditDualCertificate hd r).node_le_maxNode i).trans hN)) ≤ t) ∧
    ∀ T ∈ CertificationGaussian.signedProductFrameFamily (S := Fin n) (I := Fin d)
      (residualRadii (quditDualCertificate hd r)) (residualWeight d (quditDualCertificate hd r)),
      CertificationGaussian.gaussianFrameSphereScore T ψ ≤
        (1+6/(n:ℝ))*CertificationGaussian.kernelVarianceScale d n
          (residualRadii (quditDualCertificate hd r)) (residualWeight d (quditDualCertificate hd r))}

theorem sphere_pureTargetShell_fidelity_continuous (hd : 2 ≤ d) (j : ℕ) (hj : j ≤ n) :
    Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1 =>
      pureTargetFidelity (spherePureVector ψ) (pureTargetShell hd (spherePureVector ψ) j hj)) := by
  have ht (u : WeylLabel d n) : Continuous
      (fun ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1 =>
        Complex.normSq (inner ℂ (ψ : EuclideanSpace ℂ _)
          (Matrix.toEuclideanCLM (n := CertificationGaussian.QuditIndex d n) (𝕜 := ℂ) (quditWeyl u) ψ))) :=
    Complex.continuous_normSq.comp (continuous_subtype_val.inner
      ((Matrix.toEuclideanCLM (n := CertificationGaussian.QuditIndex d n) (𝕜 := ℂ)
        (quditWeyl u)).continuous.comp continuous_subtype_val))
  have hs := (continuous_finsetSum (weylShell d n j) (fun u _ => ht u)).const_mul
    (((weylShell d n j).card : ℝ)⁻¹)
  convert hs using 1
  ext ψ
  exact pureTargetShell_fidelity hd (spherePureVector ψ) j hj

theorem measurableDualSphereGoodEvent_isClosed (hd : 2 ≤ d) (r : ℕ)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) :
    IsClosed (measurableDualSphereGoodEvent hd r hN t) := by
  change IsClosed {ψ | (_ : Prop) ∧ (_ : Prop)}
  rw [Set.ofPred_and]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le (sphere_pureTargetShell_fidelity_continuous hd _ _) continuous_const
  · exact CertificationGaussian.isClosed_gaussianFrameSphereScore_uniform_sublevel _ _

theorem measurableDualSphereGoodEvent_isCompact (hd : 2 ≤ d) (r : ℕ)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) :
    IsCompact (measurableDualSphereGoodEvent hd r hN t) :=
  (measurableDualSphereGoodEvent_isClosed hd r hN t).isCompact

theorem measurableDualSphereGoodEvent_measurableSet (hd : 2 ≤ d) (r : ℕ)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) :
    MeasurableSet (measurableDualSphereGoodEvent hd r hN t) :=
  (measurableDualSphereGoodEvent_isClosed hd r hN t).measurableSet

/-- The Haar event is the exact preimage of the canonical compact target event. -/
def measurableDualHaarGoodEvent (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) :
    Set (CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n)) :=
  (fun U => CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) U ψ) ⁻¹'
    measurableDualSphereGoodEvent hd r hN t

theorem measurableDualHaarGoodEvent_isClosed (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) :
    IsClosed (measurableDualHaarGoodEvent hd r ψ hN t) :=
  (measurableDualSphereGoodEvent_isClosed hd r hN t).preimage
    ((CertificationGaussian.complexUnitarySphereAction_continuous _).comp
      (continuous_id.prodMk continuous_const))

theorem measurableDualHaarGoodEvent_measurableSet (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) :
    MeasurableSet (measurableDualHaarGoodEvent hd r ψ hN t) :=
  (measurableDualHaarGoodEvent_isClosed hd r ψ hN t).measurableSet

theorem measurableDualHaarGoodEvent_failure_eq (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) :
    CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
      (measurableDualHaarGoodEvent hd r ψ hN t)ᶜ =
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))
        (measurableDualSphereGoodEvent hd r hN t)ᶜ := by
  have he := congrArg (fun μ : Measure (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) =>
      μ (measurableDualSphereGoodEvent hd r hN t)ᶜ)
    (CertificationGaussian.complexUnitaryHaar_orbit_map (CertificationGaussian.QuditIndex d n) ψ)
  rw [Measure.map_apply (CertificationGaussian.complexUnitarySphereAction_continuous _).measurable.of_uncurry_right
    (measurableDualSphereGoodEvent_measurableSet hd r hN t).compl] at he
  exact he

theorem measurableDualSphereGoodEvent_low_fidelity (hd : 2 ≤ d) (r : ℕ)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ) (hD : ((d : ℝ)^n)⁻¹ ≤ t)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hψ : ψ ∈ measurableDualSphereGoodEvent hd r hN t) :
    uncalibratedLowFidelity hd r (spherePureVector ψ) hN ≤ t :=
  dualLowState_fidelity_le hd (quditDualCertificate hd r) _ hN hD hψ.1

theorem measurableDualSphereGoodEvent_residual_bound
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (hd : 2 ≤ d) (r : ℕ) (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hψ : ψ ∈ measurableDualSphereGoodEvent hd r hN t)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    dualResidualQuadratic (quditDualCertificate hd r) (spherePureVector ψ) M ≤
      (1+6/(n:ℝ))*CertificationGaussian.kernelVarianceScale d n
        (residualRadii (quditDualCertificate hd r)) (residualWeight d (quditDualCertificate hd r)) :=
  dualResidualQuadratic_le_of_frameFamily hd _ hN ψ _ hψ.2 M

theorem measurableDualSphereGoodEvent_referenceL2_cutoff
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (hd : 2 ≤ d) (r : ℕ) (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ)
    (hD : ((d : ℝ)^n)⁻¹ ≤ t)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hψ : ψ ∈ measurableDualSphereGoodEvent hd r hN t)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r (spherePureVector ψ) hN < b)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd r (spherePureVector ψ) hN b hb0 hb1) s -
      (MeasurablePOVM.product M).bornDensity (calibratedLowState hd r (spherePureVector ψ) hN b hb0 hb1 hlb) s)^2
      ∂(MeasurablePOVM.product M).traceReference) ≤
      2*(calibratedUniformWeight hd r b)^2 * (1+6/(n:ℝ)) *
        CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r)) + 4*(d:ℝ)^n*t^2 := by
  have hQ := measurableDualSphereGoodEvent_residual_bound hd r hN t ψ hψ M
  have hl := measurableDualSphereGoodEvent_low_fidelity hd r hN t hD ψ hψ
  have he := calibrated_error_bounds hd r (spherePureVector ψ) hN b hb0 hb1 hlb
  have he2 := pow_le_pow_left₀ he.1 (he.2.trans hl) 2
  refine (calibrated_product_referenceL2_sq_le_kernel hd r (spherePureVector ψ) hN b hb0 hb1 hlb M).trans ?_
  have h := add_le_add (mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 2*(calibratedUniformWeight hd r b)^2))
    (mul_le_mul_of_nonneg_left he2 (by positivity : 0 ≤ 4*(d:ℝ)^n))
  exact h.trans_eq (by ring)

theorem measurableDualSphereGoodEvent_klDiv_cutoff
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (hd : 2 ≤ d) (r : ℕ) (hN : (quditDualCertificate hd r).maxNode ≤ n) (t : ℝ)
    (hD : ((d : ℝ)^n)⁻¹ ≤ t)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hψ : ψ ∈ measurableDualSphereGoodEvent hd r hN t)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r (spherePureVector ψ) hN < b)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    klDiv ((MeasurablePOVM.product M).born (calibratedNumeratorState hd r (spherePureVector ψ) hN b hb0 hb1 hlb))
      ((MeasurablePOVM.product M).born (calibratedDenominatorState hd r (spherePureVector ψ) hN b hb0 hb1 hlb)) ≤
      ENNReal.ofReal (2*calibratedUniformWeight hd r b * (1+6/(n:ℝ)) *
        CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r)) + (4/calibratedUniformWeight hd r b)*(d:ℝ)^n*t^2) := by
  have h := calibrated_product_klDiv_le_of_bounds hd r (spherePureVector ψ) hN b hb0 hb1 hlb M _ t
    (measurableDualSphereGoodEvent_residual_bound hd r hN t ψ hψ M)
    (measurableDualSphereGoodEvent_low_fidelity hd r hN t hD ψ hψ)
  convert h using 1
  congr 1
  ring

end LocalCertification.Quantum
