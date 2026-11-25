import LocalCertification.Quantum.CalibratedDistance
import LocalCertification.Quantum.CalibrationEvent

set_option autoImplicit false
open scoped BigOperators ENNReal
open LocalCertification.Extremal Matrix MeasureTheory InformationTheory Metric Set
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

/-- Fixed parity selects the opposite state in the numerator; it is independent of the basis. -/
def calibratedNumeratorState (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    QIT.State (CertificationGaussian.QuditIndex d n) :=
  if Even r then calibratedLowState hd r ψ hN b hb0 hb1 hlb else calibratedHighState hd r ψ hN b hb0 hb1

/-- The ordered pair has actual measure KL controlled by the unique residual kernel and calibration error. -/
theorem calibrated_productBorn_klDiv (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (U : Fin n → CertificationGaussian.LocalUnitary d) :
    klDiv (productBornMeasure d n U (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
      (productBornMeasure d n U (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤
      ENNReal.ofReal (2*calibratedUniformWeight hd r b*(d : ℝ)^n*
        ‖CertificationGaussian.processedProbability (tensorBasis d n (qitProductBasis d n U))
          (CertificationGaussian.signedHammingKernel d n (residualRadii (quditDualCertificate hd r))
            (residualWeight d (quditDualCertificate hd r))) (WithLp.toLp 2 ψ.amp)‖^2 +
        4*(d : ℝ)^n/calibratedUniformWeight hd r b*
          (b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))^2) := by
  have hβ := calibratedUniformWeight_pos hd r hb1
  have hD : 0 < (d : ℝ)^n := pow_pos (by exact_mod_cast (by omega : 0 < d)) _
  have hKL := productBornMeasure_klDiv_le_floor d n U
    (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb)
    (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)
    (div_pos hβ hD) (calibrated_productBorn_denominator hd r ψ hN b hb0 hb1 hlb U)
  have heq : (∑ x, (productBorn d n U (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb) x-
      productBorn d n U (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb) x)^2) =
      ∑ x, (productBorn d n U (calibratedHighState hd r ψ hN b hb0 hb1) x-
        productBorn d n U (calibratedLowState hd r ψ hN b hb0 hb1 hlb) x)^2 := by
    unfold calibratedNumeratorState calibratedDenominatorState
    split_ifs
    · apply Finset.sum_congr rfl
      intro x _
      ring
    · rfl
  rw [heq] at hKL
  apply hKL.trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left
    (calibrated_productBorn_square_distance hd r ψ hN b hb0 hb1 hlb U)
    (inv_nonneg.mpr (div_nonneg hβ.le hD.le))
  convert h using 1
  field_simp

/-- The actual common event controls KL for every continuous product basis simultaneously. -/
theorem calibratedHaarGoodEvent_klDiv (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (C : ℝ)
    (W : CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n))
    (hW : W ∈ dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n)) (hn : 1 ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r (haarPureVector ψ W) hN < b)
    (U : Fin n → CertificationGaussian.LocalUnitary d) :
    klDiv (productBornMeasure d n U (calibratedNumeratorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb))
      (productBornMeasure d n U (calibratedDenominatorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb)) ≤
      ENNReal.ofReal (2*calibratedUniformWeight hd r b*(1+C/n)*
        CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r)) +
        (4/calibratedUniformWeight hd r b)*((n : ℝ)^6/(d : ℝ)^n)) := by
  apply (calibrated_productBorn_klDiv hd r (haarPureVector ψ W) hN b hb0 hb1 hlb U).trans
  apply ENNReal.ofReal_le_ofReal
  have hβ := calibratedUniformWeight_pos hd r hb1
  have hD : 0 < (d : ℝ)^n := pow_pos (by exact_mod_cast (by omega : 0 < d)) _
  have he := calibrated_error_bounds hd r (haarPureVector ψ W) hN b hb0 hb1 hlb
  have hl := dualHaarGoodEvent_low_fidelity hd r ψ hN C _
    (uniform_fidelity_le_dualOverlapCutoff hd hn) W hW
  have hs : (b-calibrationAlpha b (uncalibratedLowFidelity hd r (haarPureVector ψ W) hN))^2 ≤
      (dualOverlapCutoff d n)^2 :=
    (sq_le_sq₀ he.1 (dualOverlapCutoff_pos hd hn).le).mpr (he.2.trans hl)
  have h1 := mul_le_mul_of_nonneg_left (hW.2 U) (show 0 ≤ 2*calibratedUniformWeight hd r b by positivity)
  have h2 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*(d : ℝ)^n/calibratedUniformWeight hd r b by positivity)
  have hid : 4*(d : ℝ)^n/calibratedUniformWeight hd r b*(dualOverlapCutoff d n)^2 =
      (4/calibratedUniformWeight hd r b)*((n : ℝ)^6/(d : ℝ)^n) := by
    unfold dualOverlapCutoff
    field_simp
  rw [hid] at h2
  change 2*calibratedUniformWeight hd r b*(d : ℝ)^n*‖CertificationGaussian.processedProbability
    (tensorBasis d n (qitProductBasis d n U))
    (CertificationGaussian.signedHammingKernel d n (residualRadii (quditDualCertificate hd r))
      (residualWeight d (quditDualCertificate hd r)))
    (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ)‖^2 + _ ≤ _
  nlinarith [h1,h2]

end LocalCertification.Quantum
