import LocalCertification.Quantum.CalibrationFloor
import LocalCertification.Extremal.DegreeZero

/-! The exact degree-zero high state, derived from the same extremal certificate
used by the fixed-degree hierarchy.  No new choice of hard states is introduced. -/

set_option autoImplicit false
open Matrix LocalCertification.Extremal
open scoped BigOperators ComplexOrder
noncomputable section

namespace LocalCertification.Quantum

/-- Every optimal degree-zero certificate has the same two coefficients. -/
theorem degreeZero_dual_coefficients {q : ℝ} (hq : 1 < q) (c : IntegerDualCertificate q 0) :
    (∀ i, c.weight i = q) ∧ c.infinityWeight = 1-q := by
  have hw : 0 < c.weight 0 := by simpa using c.weight_sign 0
  have hi : c.infinityWeight < 0 := by
    have h := c.infinityWeight_sign
    norm_num at h
    linarith
  have hm : c.weight 0+c.infinityWeight = 1 := by simpa using c.mass
  have hv : c.weight 0-c.infinityWeight = 2*q-1 := by
    simpa [abs_of_pos hw, abs_of_neg hi, extremalValue_zero q hq, sub_eq_add_neg] using c.variation
  constructor
  · intro i
    have : i = 0 := Fin.eq_zero i
    rw [this]
    linarith
  · linarith

variable {d n : ℕ} [NeZero d]

/-- Exact original high state before calibration. -/
theorem dualHighState_zero_matrix (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) 0)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n) :
    (dualHighState hd c ψ hN).matrix =
      ((d : ℝ)+1)⁻¹ • ψ.state.matrix +
      (1-((d : ℝ)+1)⁻¹) • (quditMaximallyMixed d n).matrix := by
  let q : ℝ := (d : ℝ)+1
  have hq : 1 < q := qudit_parameter_gt_one hd
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hc := degreeZero_dual_coefficients hq c
  have hz : dualNormalization q 0 = q := by
    rw [dualNormalization, extremalValue_zero q hq]
    ring
  have hn : max (-q) 0 = 0 := max_eq_right (neg_nonpos.mpr hq0.le)
  have hi : max (-(1-q)) 0 = q-1 := by
    rw [show -(1-q) = q-1 by ring, max_eq_left (sub_nonneg.mpr hq.le)]
  have he : q⁻¹*(q-1) = 1-q⁻¹ := by field_simp [hq0.ne']
  rw [dualHighState_matrix, hz]
  simp only [hc.1, hc.2, hn, hi, zero_smul, Finset.sum_const_zero, add_zero]
  rw [smul_add, smul_smul, he]

/-- The paper's coefficient `h=b+(1-b)/q` belongs to the existing calibrated
degree-zero state, not to a separately postulated state. -/
theorem calibratedHighState_zero_matrix (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (calibratedHighState hd 0 ψ hN b hb0 hb1).matrix =
      (b+(1-b)*((d : ℝ)+1)⁻¹) • ψ.state.matrix +
      (1-(b+(1-b)*((d : ℝ)+1)⁻¹)) • (quditMaximallyMixed d n).matrix := by
  change b • ψ.state.matrix + (1-b) • (dualHighState hd (quditDualCertificate hd 0) ψ hN).matrix = _
  rw [dualHighState_zero_matrix, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
  congr 2
  ring

end LocalCertification.Quantum
