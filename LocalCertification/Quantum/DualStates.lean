import LocalCertification.Quantum.StateMixture
import LocalCertification.Quantum.WeylShellState
import LocalCertification.Extremal.ResidualMass
import LocalCertification.Extremal.DualNormalization

set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Quantum

variable {d : ℕ} [NeZero d] {n r : ℕ}

omit [NeZero d] in
theorem qudit_parameter_gt_one (hd : 2 ≤ d) : 1 < (d : ℝ)+1 := by
  exact_mod_cast (show 1 < d+1 by omega)

/-- Actual shell states followed by the QIT maximally mixed state at the infinity atom. -/
def dualAtom (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    Fin (r+2) → QIT.State (CertificationGaussian.QuditIndex d n) :=
  Fin.snoc (fun i => pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN))
    (quditMaximallyMixed d n)

/-- The high-fidelity matrix is the literal normalized target plus negative dual mass. -/
def dualHighMatrix (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ :=
  (dualNormalization ((d : ℝ)+1) r)⁻¹ •
    (ψ.state.matrix + weightedStateMatrix (dualAtom hd c ψ hN) (fun i => max (-c.coefficient i) 0))

/-- The low-fidelity matrix uses exactly the positive dual mass. -/
def dualLowMatrix (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ :=
  (dualNormalization ((d : ℝ)+1) r)⁻¹ •
    weightedStateMatrix (dualAtom hd c ψ hN) (fun i => max (c.coefficient i) 0)

theorem dualHighMatrix_pos (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualHighMatrix hd c ψ hN).PosSemidef := by
  apply (ψ.state.pos.add (weightedStateMatrix_pos _ _ (fun _ => le_max_right _ _))).smul
  exact inv_nonneg.mpr (dualNormalization_pos _ (qudit_parameter_gt_one hd) r).le

theorem dualLowMatrix_pos (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualLowMatrix hd c ψ hN).PosSemidef := by
  apply (weightedStateMatrix_pos _ _ (fun _ => le_max_right _ _)).smul
  exact inv_nonneg.mpr (dualNormalization_pos _ (qudit_parameter_gt_one hd) r).le

theorem dualHighMatrix_trace (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualHighMatrix hd c ψ hN).trace = 1 := by
  have hm : ∑ i, max (-c.coefficient i) 0 = dualNormalization ((d : ℝ)+1) r-1 := c.negative_mass
  have hZ := ne_of_gt (dualNormalization_pos _ (qudit_parameter_gt_one hd) r)
  simp only [dualHighMatrix, Matrix.trace_smul, Matrix.trace_add, ψ.state.trace_eq_one,
    weightedStateMatrix_trace, hm]
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  field_simp
  ring

theorem dualLowMatrix_trace (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualLowMatrix hd c ψ hN).trace = 1 := by
  have hm : ∑ i, max (c.coefficient i) 0 = dualNormalization ((d : ℝ)+1) r := c.positive_mass
  have hZ := ne_of_gt (dualNormalization_pos _ (qudit_parameter_gt_one hd) r)
  simp only [dualLowMatrix, Matrix.trace_smul, weightedStateMatrix_trace, hm]
  rw [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hZ, Complex.ofReal_one]

/-- A genuine QIT high-fidelity state; positivity and trace one are proved from the actual dual. -/
def dualHighState (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    QIT.State (CertificationGaussian.QuditIndex d n) where
  matrix := dualHighMatrix hd c ψ hN
  pos := dualHighMatrix_pos hd c ψ hN
  trace_eq_one := dualHighMatrix_trace hd c ψ hN

/-- A genuine QIT low-fidelity state from the same certificate and target. -/
def dualLowState (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    QIT.State (CertificationGaussian.QuditIndex d n) where
  matrix := dualLowMatrix hd c ψ hN
  pos := dualLowMatrix_pos hd c ψ hN
  trace_eq_one := dualLowMatrix_trace hd c ψ hN

/-- The high state has at least the actual extremal fidelity gap, before calibration. -/
theorem dualHighState_fidelity_lower (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    gamma ((d : ℝ)+1) r ≤ pureTargetFidelity ψ (dualHighState hd c ψ hN) := by
  have hpos : 0 ≤ ∑ i, max (-c.coefficient i) 0 * pureTargetFidelity ψ (dualAtom hd c ψ hN i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (le_max_right _ _) (pureTargetFidelity_nonneg _ _))
  change _ ≤ (ψ.state.matrix * dualHighMatrix hd c ψ hN).trace.re
  simp only [dualHighMatrix, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
    Complex.smul_re, Complex.add_re, smul_eq_mul, weightedStateMatrix_pairing,
    ψ.state_matrix_mul_self, ψ.state.trace_eq_one, Complex.one_re]
  rw [dualNormalization_inv _ (qudit_parameter_gt_one hd) r]
  nlinarith [gamma_pos ((d : ℝ)+1) (qudit_parameter_gt_one hd) r]

/-- The literal high-state formula, displaying finite shells and the infinity uniform component. -/
theorem dualHighState_matrix (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualHighState hd c ψ hN).matrix = (dualNormalization ((d : ℝ)+1) r)⁻¹ •
      (ψ.state.matrix + (∑ i, max (-c.weight i) 0 •
        (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)).matrix) +
        max (-c.infinityWeight) 0 • (quditMaximallyMixed d n).matrix) := by
  simp [dualHighState, dualHighMatrix, weightedStateMatrix, Fin.sum_univ_castSucc,
    IntegerDualCertificate.coefficient, dualAtom, add_assoc]

/-- The literal low-state formula from positive dual coefficients. -/
theorem dualLowState_matrix (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualLowState hd c ψ hN).matrix = (dualNormalization ((d : ℝ)+1) r)⁻¹ •
      ((∑ i, max (c.weight i) 0 •
        (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)).matrix) +
        max (c.infinityWeight) 0 • (quditMaximallyMixed d n).matrix) := by
  simp [dualLowState, dualLowMatrix, weightedStateMatrix, Fin.sum_univ_castSucc,
    IntegerDualCertificate.coefficient, dualAtom]

/-- Subtracting the actual positive states recovers the signed dual, without positivity of residual weights. -/
theorem dualStates_difference (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualHighState hd c ψ hN).matrix - (dualLowState hd c ψ hN).matrix =
      (dualNormalization ((d : ℝ)+1) r)⁻¹ •
        (ψ.state.matrix - weightedStateMatrix (dualAtom hd c ψ hN) c.coefficient) := by
  have hm (a : ℝ) : max (-a) 0 - max a 0 = -a := by
    rcases le_total 0 a with h | h
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  have hw : weightedStateMatrix (dualAtom hd c ψ hN) (fun i => max (-c.coefficient i) 0) -
      weightedStateMatrix (dualAtom hd c ψ hN) (fun i => max (c.coefficient i) 0) =
        -weightedStateMatrix (dualAtom hd c ψ hN) c.coefficient := by
    unfold weightedStateMatrix
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_smul, hm, neg_smul]
    rw [Finset.sum_neg_distrib]
  change _ • (_+_) - _ • _ = _
  rw [← smul_sub, add_sub_assoc, hw, sub_eq_add_neg]

/-- The matrix-level raw difference is exactly the paper's P minus finite shells minus infinity mass. -/
theorem dualStates_difference_explicit (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualHighState hd c ψ hN).matrix - (dualLowState hd c ψ hN).matrix =
      (dualNormalization ((d : ℝ)+1) r)⁻¹ •
        (ψ.state.matrix - (∑ i, c.weight i •
          (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)).matrix) -
          c.infinityWeight • (quditMaximallyMixed d n).matrix) := by
  rw [dualStates_difference]
  simp [weightedStateMatrix, Fin.sum_univ_castSucc, IntegerDualCertificate.coefficient,
    dualAtom, sub_sub]

/-- Removing the displayed high-state uniform component leaves a positive matrix. -/
theorem dualHighState_uniform_floor (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    ((dualHighState hd c ψ hN).matrix -
      (max (-c.infinityWeight) 0 / dualNormalization ((d : ℝ)+1) r) •
        (quditMaximallyMixed d n).matrix).PosSemidef := by
  rw [dualHighState_matrix]
  have he : (dualNormalization ((d : ℝ)+1) r)⁻¹ •
      (ψ.state.matrix + (∑ i, max (-c.weight i) 0 •
        (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)).matrix) +
        max (-c.infinityWeight) 0 • (quditMaximallyMixed d n).matrix) -
      (max (-c.infinityWeight) 0 / dualNormalization ((d : ℝ)+1) r) •
        (quditMaximallyMixed d n).matrix =
      (dualNormalization ((d : ℝ)+1) r)⁻¹ •
        (ψ.state.matrix + (∑ i, max (-c.weight i) 0 •
          (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)).matrix)) := by
    rw [smul_add, smul_smul, div_eq_mul_inv, mul_comm (max (-c.infinityWeight) 0), add_sub_cancel_right]
  rw [he]
  apply (ψ.state.pos.add (Matrix.posSemidef_sum Finset.univ (fun i _ =>
    (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)).pos.smul (le_max_right _ _)))).smul
  exact inv_nonneg.mpr (dualNormalization_pos _ (qudit_parameter_gt_one hd) r).le

/-- The corresponding low-state uniform component is also a literal positive summand. -/
theorem dualLowState_uniform_floor (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    ((dualLowState hd c ψ hN).matrix -
      (max (c.infinityWeight) 0 / dualNormalization ((d : ℝ)+1) r) •
        (quditMaximallyMixed d n).matrix).PosSemidef := by
  rw [dualLowState_matrix, smul_add, smul_smul, div_eq_mul_inv,
    mul_comm (max (c.infinityWeight) 0), add_sub_cancel_right]
  apply (Matrix.posSemidef_sum Finset.univ (fun i _ =>
    (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)).pos.smul (le_max_right _ _))).smul
  exact inv_nonneg.mpr (dualNormalization_pos _ (qudit_parameter_gt_one hd) r).le

/-- Even r places the strictly positive uniform mass in the high state. -/
theorem dualHighState_uniform_floor_even (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) (hr : Even r) :
    ((dualHighState hd c ψ hN).matrix - uniformComponentWeight c •
      (quditMaximallyMixed d n).matrix).PosSemidef := by
  have hs := c.infinityWeight_sign
  rw [pow_succ, hr.neg_one_pow, one_mul] at hs
  have hi : c.infinityWeight < 0 := by linarith
  simpa only [uniformComponentWeight, max_eq_left (neg_nonneg.mpr hi.le), abs_of_neg hi] using
    dualHighState_uniform_floor hd c ψ hN

/-- Odd r places the strictly positive uniform mass in the low state. -/
theorem dualLowState_uniform_floor_odd (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) (hr : Odd r) :
    ((dualLowState hd c ψ hN).matrix - uniformComponentWeight c •
      (quditMaximallyMixed d n).matrix).PosSemidef := by
  have hs := c.infinityWeight_sign
  rw [pow_succ, hr.neg_one_pow] at hs
  have hi : 0 < c.infinityWeight := by nlinarith
  simpa only [uniformComponentWeight, max_eq_left hi.le, abs_of_pos hi] using
    dualLowState_uniform_floor hd c ψ hN

/-- Small fidelity of the actual finite shells and the uniform atom controls the low mixture. -/
theorem dualLowState_fidelity_le (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) {ε : ℝ}
    (hε : ((d : ℝ)^n)⁻¹ ≤ ε)
    (hψ : ∀ i, pureTargetFidelity ψ
      (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)) ≤ ε) :
    pureTargetFidelity ψ (dualLowState hd c ψ hN) ≤ ε := by
  have hA (i : Fin (r+2)) : pureTargetFidelity ψ (dualAtom hd c ψ hN i) ≤ ε := by
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa [dualAtom, quditMaximallyMixed_fidelity] using hε
    · simpa [dualAtom] using hψ k
  have hZ := dualNormalization_pos _ (qudit_parameter_gt_one hd) r
  have hm : ∑ i, max (c.coefficient i) 0 = dualNormalization ((d : ℝ)+1) r := c.positive_mass
  change (ψ.state.matrix * dualLowMatrix hd c ψ hN).trace.re ≤ ε
  simp only [dualLowMatrix, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re,
    smul_eq_mul, weightedStateMatrix_pairing]
  calc
    _ ≤ (dualNormalization ((d : ℝ)+1) r)⁻¹ * ∑ i, max (c.coefficient i) 0 * ε := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hA i) (le_max_right _ _))
    _ = ε := by rw [← Finset.sum_mul, hm, ← mul_assoc, inv_mul_cancel₀ hZ.ne', one_mul]

end LocalCertification.Quantum
