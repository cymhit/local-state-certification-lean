import LocalCertification.Quantum.MeasurableDualInformation
import LocalCertification.Quantum.MeasurablePOVMCalibration

/-! Calibrated original-product information with the exact retained background.
The target and calibrated physical pair are fixed before the arbitrary local POVMs.
The kernel contribution and original shell-overlap correction remain separate. -/

open MeasureTheory Matrix InformationTheory LocalCertification.Extremal
open scoped ENNReal ComplexOrder
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ}

/-- The signed residual coefficient has exactly the square of the retained background. -/
theorem calibrated_residual_coefficient_sq (hd : 2 ≤ d) (r : ℕ) (b : ℝ) :
    (1-b)^2 * ((quditDualCertificate hd r).infinityWeight /
      dualNormalization ((d : ℝ)+1) r)^2 = (calibratedUniformWeight hd r b)^2 := by
  change (1-b)^2 * ((quditDualCertificate hd r).infinityWeight /
    dualNormalization ((d : ℝ)+1) r)^2 =
      ((1-b) * (|(quditDualCertificate hd r).infinityWeight| /
        dualNormalization ((d : ℝ)+1) r))^2
  simp only [mul_pow, div_pow, sq_abs]

variable [NeZero d] {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]

private theorem calibrated_refined_raw_term (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    2*(1-b)^2 * (∫ s,
      ((MeasurablePOVM.productRefined M).bornDensity (dualHighState hd (quditDualCertificate hd r) ψ hN) s -
       (MeasurablePOVM.productRefined M).bornDensity (dualLowState hd (quditDualCertificate hd r) ψ hN) s)^2
        ∂(MeasurablePOVM.productRefined M).traceReference) =
      2*(calibratedUniformWeight hd r b)^2 * dualResidualQuadratic (quditDualCertificate hd r) ψ M := by
  rw [MeasurablePOVM.productRefined_reference_sq_eq, dualStates_refined_difference_sq_integral,
    ← calibrated_residual_coefficient_sq]
  ring

/-- The refined rank-one reference norm has the exact residual and calibration
coefficients on the original target and its calibrated high/low pair. -/
theorem calibrated_refined_referenceL2_le_kernel (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    Real.sqrt (∫ s, ((MeasurablePOVM.productRefined M).bornDensity
      (calibratedHighState hd r ψ hN b hb0 hb1) s -
      (MeasurablePOVM.productRefined M).bornDensity
      (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s)^2
      ∂(MeasurablePOVM.productRefined M).traceReference) ≤
      calibratedUniformWeight hd r b * Real.sqrt (dualResidualQuadratic (quditDualCertificate hd r) ψ M) +
        (b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)) * Real.sqrt (2*(d:ℝ)^n) := by
  let raw := ∫ s, ((MeasurablePOVM.productRefined M).bornDensity
    (dualHighState hd (quditDualCertificate hd r) ψ hN) s -
    (MeasurablePOVM.productRefined M).bornDensity
    (dualLowState hd (quditDualCertificate hd r) ψ hN) s)^2 ∂(MeasurablePOVM.productRefined M).traceReference
  let R := dualResidualQuadratic (quditDualCertificate hd r) ψ M
  let β := calibratedUniformWeight hd r b
  have hβ : 0 < β := calibratedUniformWeight_pos hd r hb1
  have hid := calibrated_refined_raw_term hd r ψ hN b M
  change 2*(1-b)^2 * raw = 2*β^2 * R at hid
  have hscale := congrArg Real.sqrt (show (1-b)^2 * raw = β^2 * R by linarith)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sub_nonneg.mpr hb1.le),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ.le] at hscale
  have h := (MeasurablePOVM.productRefined M).calibrated_referenceL2 hd r ψ hN b hb0 hb1 hlb
  change _ ≤ (1-b) * Real.sqrt raw + _ at h
  rwa [hscale] at h

/-- The same two-term bound holds on the unrefined product outcome space. -/
theorem calibrated_product_referenceL2_le_kernel (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    Real.sqrt (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd r ψ hN b hb0 hb1) s -
      (MeasurablePOVM.product M).bornDensity (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s)^2
      ∂(MeasurablePOVM.product M).traceReference) ≤
      calibratedUniformWeight hd r b * Real.sqrt (dualResidualQuadratic (quditDualCertificate hd r) ψ M) +
        (b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)) * Real.sqrt (2*(d:ℝ)^n) := by
  have hf := calibrated_refined_referenceL2_le_kernel hd r ψ hN b hb0 hb1 hlb M
  rw [MeasurablePOVM.productRefined_reference_sq_eq] at hf
  exact (Real.sqrt_le_sqrt (MeasurablePOVM.product_referenceL2_sq_le_localRefinement M _ _)).trans hf

/-- Actual calibrated reference distance for every arbitrary-outcome product measurement. -/
theorem calibrated_product_referenceL2_sq_le_kernel (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd r ψ hN b hb0 hb1) s -
      (MeasurablePOVM.product M).bornDensity (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s)^2
        ∂(MeasurablePOVM.product M).traceReference) ≤
      2*(calibratedUniformWeight hd r b)^2 * dualResidualQuadratic (quditDualCertificate hd r) ψ M +
        4*(d : ℝ)^n*(b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))^2 := by
  let R := dualResidualQuadratic (quditDualCertificate hd r) ψ M
  let β := calibratedUniformWeight hd r b
  let e := b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)
  have hR : 0 ≤ R := mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  have hD : 0 ≤ 2*(d:ℝ)^n := by positivity
  have h := calibrated_product_referenceL2_le_kernel hd r ψ hN b hb0 hb1 hlb M
  change _ ≤ β * Real.sqrt R + e * Real.sqrt (2*(d:ℝ)^n) at h
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hs
  refine hs.trans ?_
  calc
    _ ≤ 2*(β * Real.sqrt R)^2 + 2*(e * Real.sqrt (2*(d:ℝ)^n))^2 := by
      nlinarith [sq_nonneg (β * Real.sqrt R - e*Real.sqrt (2*(d:ℝ)^n))]
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hR, Real.sq_sqrt hD]; dsimp only [β,R,e]; ring

/-- The original ordered Born laws satisfy the exact background-weighted kernel bound. -/
theorem calibrated_product_klDiv_le_kernel (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    klDiv ((MeasurablePOVM.product M).born (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
      ((MeasurablePOVM.product M).born (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤
      ENNReal.ofReal (2*calibratedUniformWeight hd r b *
        dualResidualQuadratic (quditDualCertificate hd r) ψ M +
          (4/calibratedUniformWeight hd r b)*(d : ℝ)^n*
            (b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))^2) := by
  have hβ := calibratedUniformWeight_pos hd r hb1
  have h := (MeasurablePOVM.productRefined M).calibrated_born_klDiv hd r ψ hN b hb0 hb1 hlb
  rw [calibrated_refined_raw_term] at h
  have he : (calibratedUniformWeight hd r b)⁻¹ *
      (2*(calibratedUniformWeight hd r b)^2 * dualResidualQuadratic (quditDualCertificate hd r) ψ M +
        4*(d : ℝ)^n*(b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))^2) =
      2*calibratedUniformWeight hd r b * dualResidualQuadratic (quditDualCertificate hd r) ψ M +
        (4/calibratedUniformWeight hd r b)*(d : ℝ)^n*
          (b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))^2 := by
    field_simp [hβ.ne']
  rw [he] at h
  exact (MeasurablePOVM.product_klDiv_le_localRefinement M _ _).trans h

/-- Only the original low-state overlap is needed to control calibration error. -/
theorem calibrated_product_klDiv_le_overlap (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
    klDiv ((MeasurablePOVM.product M).born (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
      ((MeasurablePOVM.product M).born (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤
      ENNReal.ofReal (2*calibratedUniformWeight hd r b *
        dualResidualQuadratic (quditDualCertificate hd r) ψ M +
          (4/calibratedUniformWeight hd r b)*(d : ℝ)^n*(uncalibratedLowFidelity hd r ψ hN)^2) := by
  have he := calibrated_error_bounds hd r ψ hN b hb0 hb1 hlb
  have he2 := pow_le_pow_left₀ he.1 he.2 2
  have hβ := calibratedUniformWeight_pos hd r hb1
  refine (calibrated_product_klDiv_le_kernel hd r ψ hN b hb0 hb1 hlb M).trans
    (ENNReal.ofReal_le_ofReal (add_le_add le_rfl ?_))
  exact mul_le_mul_of_nonneg_left he2 (by positivity)

/-- A separate kernel and shell-overlap bound instantiate the same fixed calibrated pair. -/
theorem calibrated_product_klDiv_le_of_bounds (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) (H L : ℝ)
    (hH : dualResidualQuadratic (quditDualCertificate hd r) ψ M ≤ H)
    (hL : uncalibratedLowFidelity hd r ψ hN ≤ L) :
    klDiv ((MeasurablePOVM.product M).born (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
      ((MeasurablePOVM.product M).born (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤
      ENNReal.ofReal (2*calibratedUniformWeight hd r b * H +
        (4/calibratedUniformWeight hd r b)*(d : ℝ)^n*L^2) := by
  have hβ := calibratedUniformWeight_pos hd r hb1
  have hL2 := pow_le_pow_left₀ (pureTargetFidelity_nonneg ψ
    (dualLowState hd (quditDualCertificate hd r) ψ hN)) hL 2
  refine (calibrated_product_klDiv_le_overlap hd r ψ hN b hb0 hb1 hlb M).trans
    (ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_))
  · exact mul_le_mul_of_nonneg_left hH (by positivity)
  · exact mul_le_mul_of_nonneg_left hL2 (by positivity)

end LocalCertification.Quantum
