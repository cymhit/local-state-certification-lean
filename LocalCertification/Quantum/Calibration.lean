import LocalCertification.Quantum.CalibrationBase
import LocalCertification.Quantum.DualReadout

set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Quantum

variable {d : ℕ} [NeZero d] {n : ℕ}

omit [NeZero d] in
/-- The actual certificate is chosen once from the proved extremal theorem, using only d and r. -/
def quditDualCertificate (hd : 2 ≤ d) (r : ℕ) : IntegerDualCertificate ((d : ℝ)+1) r :=
  extremalIntegerDual ((d : ℝ)+1) (qudit_parameter_gt_one hd) r

/-- Actual low-state overlap for that fixed choice, with no independently chosen certificate fields. -/
def uncalibratedLowFidelity (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n) : ℝ :=
  pureTargetFidelity ψ (dualLowState hd (quditDualCertificate hd r) ψ hN)

/-- The high state uses the requested baseline b itself as the target-mixture weight. -/
def calibratedHighState (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : QIT.State (CertificationGaussian.QuditIndex d n) :=
  targetMixture ψ (dualHighState hd (quditDualCertificate hd r) ψ hN) b hb0.le hb1.le

/-- The low state is calibrated to fidelity exactly b using its actual overlap. -/
def calibratedLowState (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    QIT.State (CertificationGaussian.QuditIndex d n) :=
  targetMixture ψ (dualLowState hd (quditDualCertificate hd r) ψ hN)
    (calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))
    (calibrationAlpha_bounds (b := b) (l := uncalibratedLowFidelity hd r ψ hN) hb0 hb1 (pureTargetFidelity_nonneg _ _) hlb).1
    ((calibrationAlpha_bounds (b := b) (l := uncalibratedLowFidelity hd r ψ hN) hb0 hb1 (pureTargetFidelity_nonneg _ _) hlb).2.trans hb1.le)

/-- The lower promise is exact, not asymptotic or approximate. -/
theorem calibratedLowState_fidelity (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    pureTargetFidelity ψ (calibratedLowState hd r ψ hN b hb0 hb1 hlb) = b := by
  unfold calibratedLowState
  rw [targetMixture_fidelity]
  exact calibrationAlpha_exact (hlb.trans hb1)

/-- The upper promise reaches the exact original extremal boundary. -/
theorem calibratedHighState_fidelity (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    b+(1-b)*gamma ((d : ℝ)+1) r ≤ pureTargetFidelity ψ (calibratedHighState hd r ψ hN b hb0 hb1) := by
  unfold calibratedHighState
  rw [targetMixture_fidelity]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (dualHighState_fidelity_lower hd (quditDualCertificate hd r) ψ hN) (sub_nonneg.mpr hb1.le))

/-- Every window at or below the threshold, including equality, is a genuine pair of promises. -/
theorem calibrated_exact_window (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (a b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (hgap : (a-b)/(1-b) ≤ gamma ((d : ℝ)+1) r) :
    pureTargetFidelity ψ (calibratedLowState hd r ψ hN b hb0 hb1 hlb) = b ∧
      a ≤ pureTargetFidelity ψ (calibratedHighState hd r ψ hN b hb0 hb1) := by
  refine ⟨calibratedLowState_fidelity hd r ψ hN b hb0 hb1 hlb, ?_⟩
  have h := (div_le_iff₀ (sub_pos.mpr hb1)).mp hgap
  have hh := calibratedHighState_fidelity hd r ψ hN b hb0 hb1
  nlinarith

/-- The correction is at most the actual low-state overlap; this strengthens the paper's 2*l bound. -/
theorem calibrated_error_bounds (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    0 ≤ b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN) ∧
      b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN) ≤ uncalibratedLowFidelity hd r ψ hN :=
  calibrationError_bounds hb0 hb1 (pureTargetFidelity_nonneg _ _) hlb

/-- Exact calibrated Born difference for every basis and outcome, before applying a norm bound. -/
theorem calibrated_productBorn_difference (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U (calibratedHighState hd r ψ hN b hb0 hb1) x -
      productBorn d n U (calibratedLowState hd r ψ hN b hb0 hb1 hlb) x =
      (1-b)*(productBorn d n U (dualHighState hd (quditDualCertificate hd r) ψ hN) x -
        productBorn d n U (dualLowState hd (quditDualCertificate hd r) ψ hN) x) +
      (b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))*
        (productBorn d n U ψ.state x - productBorn d n U
          (dualLowState hd (quditDualCertificate hd r) ψ hN) x) := by
  change basisBorn _ (targetMixture _ _ _ _ _) x - basisBorn _ (targetMixture _ _ _ _ _) x = _
  rw [targetMixture_basisBorn, targetMixture_basisBorn]
  simp only [productBorn, productBasisPOVM, basisBorn]
  ring

end LocalCertification.Quantum
