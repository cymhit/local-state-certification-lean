import LocalCertification.Quantum.CalibrationFloor
import LocalCertification.Quantum.BornMeasure

set_option autoImplicit false
open scoped BigOperators ENNReal
open LocalCertification.Extremal Matrix MeasureTheory InformationTheory
noncomputable section
namespace LocalCertification.Quantum

/-- Two genuine finite probability vectors have squared Euclidean distance at most two. -/
theorem probability_square_distance_le_two {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) :
    ∑ i, (p i-q i)^2 ≤ 2 := by
  classical
  calc
    _ ≤ ∑ i, (p i+q i) := by
      apply Finset.sum_le_sum
      intro i _
      have hp1 : p i ≤ 1 := (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)).trans_eq hpsum
      have hq1 : q i ≤ 1 := (Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)).trans_eq hqsum
      nlinarith [mul_nonneg (hp i) (hq i), mul_nonneg (hp i) (sub_nonneg.mpr hp1),
        mul_nonneg (hq i) (sub_nonneg.mpr hq1)]
    _ = 2 := by rw [Finset.sum_add_distrib,hpsum,hqsum]; norm_num

/-- The same unique processed-probability vector has exactly the physical QIT Born coordinates. -/
theorem productBorn_processed_norm_sq (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (R : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℝ) :
    ∑ x, (R.mulVec (productBorn d n U ψ.state) x-((d : ℝ)^n)⁻¹)^2 =
      ‖CertificationGaussian.processedProbability (tensorBasis d n (qitProductBasis d n U)) R
        (WithLp.toLp 2 ψ.amp)‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  rw [CertificationGaussian.Consumers.processedProbability_coordinate, CertificationGaussian.qudit_card, Nat.cast_pow]
  simp only [Matrix.mulVec, dotProduct, productBorn_pure]

variable {d n : ℕ} [NeZero d]

omit [NeZero d] in
/-- Squaring removes the proven parity sign while keeping the fixed physical uniform weight. -/
theorem calibratedSignalWeight_sq (hd : 2 ≤ d) (r : ℕ) (b : ℝ) :
    ((1-b)*((quditDualCertificate hd r).infinityWeight/dualNormalization ((d : ℝ)+1) r))^2 =
      (calibratedUniformWeight hd r b)^2 := by
  unfold calibratedUniformWeight uniformComponentWeight
  rw [mul_pow,mul_pow,div_pow,div_pow,sq_abs]

/-- A direct squared-distance estimate for the actual calibrated readouts in every product basis. -/
theorem calibrated_productBorn_square_distance (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (U : Fin n → CertificationGaussian.LocalUnitary d) :
    ∑ x, (productBorn d n U (calibratedHighState hd r ψ hN b hb0 hb1) x-
      productBorn d n U (calibratedLowState hd r ψ hN b hb0 hb1 hlb) x)^2 ≤
      2*(calibratedUniformWeight hd r b)^2*
        ‖CertificationGaussian.processedProbability (tensorBasis d n (qitProductBasis d n U))
          (CertificationGaussian.signedHammingKernel d n (residualRadii (quditDualCertificate hd r))
            (residualWeight d (quditDualCertificate hd r))) (WithLp.toLp 2 ψ.amp)‖^2 +
      4*(b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))^2 := by
  let a := (1-b)*((quditDualCertificate hd r).infinityWeight/dualNormalization ((d : ℝ)+1) r)
  let e := b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)
  let f := fun x => (CertificationGaussian.signedHammingKernel d n (residualRadii (quditDualCertificate hd r))
      (residualWeight d (quditDualCertificate hd r))).mulVec (productBorn d n U ψ.state) x-((d : ℝ)^n)⁻¹
  let g := fun x => productBorn d n U ψ.state x-
      productBorn d n U (dualLowState hd (quditDualCertificate hd r) ψ hN) x
  have heq x : productBorn d n U (calibratedHighState hd r ψ hN b hb0 hb1) x-
      productBorn d n U (calibratedLowState hd r ψ hN b hb0 hb1 hlb) x = a*f x+e*g x := by
    rw [calibrated_productBorn_difference, dualStates_productBorn_difference]
    dsimp only [a,e,f,g]
    ring
  have hg : ∑ x, (g x)^2 ≤ 2 := probability_square_distance_le_two _ _
    (productBorn_nonneg _ _ _ _) (productBorn_nonneg _ _ _ _) (productBorn_sum _ _ _ _) (productBorn_sum _ _ _ _)
  have hsum : ∑ x, (a*f x+e*g x)^2 ≤ 2*a^2*(∑ x, (f x)^2)+2*e^2*(∑ x,(g x)^2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    nlinarith [sq_nonneg (a*f x-e*g x)]
  simp_rw [heq]
  apply hsum.trans
  have hf : ∑ x, (f x)^2 = ‖CertificationGaussian.processedProbability
      (tensorBasis d n (qitProductBasis d n U))
      (CertificationGaussian.signedHammingKernel d n (residualRadii (quditDualCertificate hd r))
        (residualWeight d (quditDualCertificate hd r))) (WithLp.toLp 2 ψ.amp)‖^2 :=
    productBorn_processed_norm_sq d n U ψ _
  rw [hf, show a^2 = (calibratedUniformWeight hd r b)^2 from calibratedSignalWeight_sq hd r b]
  have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*e^2 by positivity)
  dsimp only [e] at *
  linarith

end LocalCertification.Quantum
