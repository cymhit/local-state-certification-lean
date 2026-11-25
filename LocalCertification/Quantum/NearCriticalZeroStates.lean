import LocalCertification.Quantum.DegreeZeroState
import LocalCertification.Quantum.MeasurablePOVMCalibration

/-! The actual degree-zero nearcritical high state.  It mixes the existing
calibrated high state with the target and retains the original calibrated low
state.  All density differences use the original POVM trace reference. -/

set_option autoImplicit false
open MeasureTheory Matrix InformationTheory LocalCertification.Extremal
open scoped ENNReal ComplexOrder
noncomputable section

namespace LocalCertification.Quantum

def zeroMixingWeight (q ε : ℝ) : ℝ := ε/(1-q⁻¹)

theorem zeroMixingGap_pos {q : ℝ} (hq : 1 < q) : 0 < 1-q⁻¹ := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hi := inv_pos.mpr hq0
  have hm := mul_inv_cancel₀ hq0.ne'
  nlinarith

theorem zeroMixingWeight_bounds {q ε : ℝ} (hq : 1 < q)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-q⁻¹)/2) :
    0 ≤ zeroMixingWeight q ε ∧ zeroMixingWeight q ε ≤ 1/2 := by
  have hg := zeroMixingGap_pos hq
  refine ⟨div_nonneg hε0 hg.le, (div_le_iff₀ hg).mpr ?_⟩
  linarith

theorem zeroMixingWeight_identity {q : ℝ} (hq : 1 < q) (b ε : ℝ) :
    zeroMixingWeight q ε * (1-(b+(1-b)*q⁻¹)) = (1-b)*ε := by
  have hg := zeroMixingGap_pos hq
  rw [show 1-(b+(1-b)*q⁻¹) = (1-b)*(1-q⁻¹) by ring]
  unfold zeroMixingWeight
  rw [div_eq_mul_inv]
  calc
    ε * (1-q⁻¹)⁻¹ * ((1-b)*(1-q⁻¹)) =
        (1-b)*ε*((1-q⁻¹)⁻¹*(1-q⁻¹)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hg.ne', mul_one]

theorem zeroHighCoefficient_bounds {q b : ℝ} (hq : 1 < q) (hb0 : 0 < b) (hb1 : b < 1) :
    0 < b+(1-b)*q⁻¹ ∧ b+(1-b)*q⁻¹ < 1 := by
  have hg := zeroMixingGap_pos hq
  have hi : 0 < q⁻¹ := inv_pos.mpr (zero_lt_one.trans hq)
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hb1) hi]
  · nlinarith [mul_pos (sub_pos.mpr hb1) hg]

variable {d n : ℕ} [NeZero d]

/-- A literal mixture of the already defined calibrated high state and target. -/
def nearCriticalZeroHighState (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2) :
    QIT.State (CertificationGaussian.QuditIndex d n) :=
  binaryMixture (calibratedHighState hd 0 ψ hN b hb0 hb1) ψ.state
    (zeroMixingWeight ((d : ℝ)+1) ε)
    (zeroMixingWeight_bounds (qudit_parameter_gt_one hd) hε0 hε1).1
    ((zeroMixingWeight_bounds (qudit_parameter_gt_one hd) hε0 hε1).2.trans (by norm_num))

theorem nearCriticalZeroHighState_matrix (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2) :
    (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1).matrix =
      (b+(1-b)*((d : ℝ)+1)⁻¹+(1-b)*ε) • ψ.state.matrix +
      (1-(b+(1-b)*((d : ℝ)+1)⁻¹)-(1-b)*ε) • (quditMaximallyMixed d n).matrix := by
  let h := b+(1-b)*((d : ℝ)+1)⁻¹
  let t := zeroMixingWeight ((d : ℝ)+1) ε
  have he : t*(1-h) = (1-b)*ε := zeroMixingWeight_identity (qudit_parameter_gt_one hd) b ε
  have hp : (1-t)*h+t = h+(1-b)*ε := by nlinarith
  have hm : (1-t)*(1-h) = 1-h-(1-b)*ε := by nlinarith
  change (1-t) • (calibratedHighState hd 0 ψ hN b hb0 hb1).matrix + t • ψ.state.matrix = _
  rw [calibratedHighState_zero_matrix, smul_add, smul_smul, smul_smul, add_right_comm, ← add_smul]
  change ((1-t)*h+t) • ψ.state.matrix + ((1-t)*(1-h)) • (quditMaximallyMixed d n).matrix = _
  rw [hp, hm]

/-- The exact difference in the paper, valid against any fixed low state. -/
theorem nearCriticalZeroHighState_difference (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1).matrix - ρ.matrix =
      ((calibratedHighState hd 0 ψ hN b hb0 hb1).matrix - ρ.matrix) +
      ((1-b)*ε) • (ψ.state.matrix-(quditMaximallyMixed d n).matrix) := by
  rw [nearCriticalZeroHighState_matrix, calibratedHighState_zero_matrix,
    add_smul, sub_smul, smul_sub]
  abel

theorem nearCriticalZeroHighState_floor (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2) :
    ((nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1).matrix -
      ((1-(b+(1-b)*((d : ℝ)+1)⁻¹))/2) • (quditMaximallyMixed d n).matrix).PosSemidef := by
  let h := b+(1-b)*((d : ℝ)+1)⁻¹
  let c := (1-b)*ε
  have hh : 0 < h ∧ h < 1 := zeroHighCoefficient_bounds (qudit_parameter_gt_one hd) hb0 hb1
  have hc : 0 ≤ c := mul_nonneg (sub_nonneg.mpr hb1.le) hε0
  have he : zeroMixingWeight ((d : ℝ)+1) ε * (1-h) = c :=
    zeroMixingWeight_identity (qudit_parameter_gt_one hd) b ε
  have ht := (zeroMixingWeight_bounds (qudit_parameter_gt_one hd) hε0 hε1).2
  have hc1 : 0 ≤ 1-h-c-(1-h)/2 := by nlinarith
  have hp := (ψ.state.pos.smul (show 0 ≤ h+c by linarith)).add
    ((quditMaximallyMixed d n).pos.smul hc1)
  rw [nearCriticalZeroHighState_matrix]
  convert hp using 1
  change (h+c) • ψ.state.matrix + (1-h-c) • (quditMaximallyMixed d n).matrix -
    ((1-h)/2) • (quditMaximallyMixed d n).matrix = _
  rw [add_sub_assoc, ← sub_smul]

/-- The actual mixed high state reaches the moving fidelity promise. -/
theorem nearCriticalZeroHighState_fidelity (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2) :
    b+(1-b)*(((d : ℝ)+1)⁻¹+ε) ≤
      pureTargetFidelity ψ (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1) := by
  let h := b+(1-b)*((d : ℝ)+1)⁻¹
  let t := zeroMixingWeight ((d : ℝ)+1) ε
  have ht := zeroMixingWeight_bounds (qudit_parameter_gt_one hd) hε0 hε1
  have he : t*(1-h) = (1-b)*ε := zeroMixingWeight_identity (qudit_parameter_gt_one hd) b ε
  have hh : h ≤ pureTargetFidelity ψ (calibratedHighState hd 0 ψ hN b hb0 hb1) := by
    simpa only [gamma_zero _ (qudit_parameter_gt_one hd)] using
      calibratedHighState_fidelity hd 0 ψ hN b hb0 hb1
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1-t by dsimp [t]; linarith [ht.2])
  unfold nearCriticalZeroHighState
  rw [binaryMixture_fidelity, pureTargetFidelity_self, mul_one]
  change _ ≤ (1-t) * pureTargetFidelity ψ (calibratedHighState hd 0 ψ hN b hb0 hb1)+t
  dsimp only [h] at he
  nlinarith

/-- On the nonpositive side, the original calibrated pair keeps both promises. -/
theorem calibratedZero_promises_nonpositive (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd 0 ψ hN < b) (ε : ℝ) (hε : ε ≤ 0) :
    pureTargetFidelity ψ (calibratedLowState hd 0 ψ hN b hb0 hb1 hlb) = b ∧
      b+(1-b)*(((d : ℝ)+1)⁻¹+ε) ≤
        pureTargetFidelity ψ (calibratedHighState hd 0 ψ hN b hb0 hb1) := by
  refine ⟨calibratedLowState_fidelity hd 0 ψ hN b hb0 hb1 hlb, ?_⟩
  have hh := calibratedHighState_fidelity hd 0 ψ hN b hb0 hb1
  rw [gamma_zero _ (qudit_parameter_gt_one hd)] at hh
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hb1.le) hε]

namespace MeasurablePOVM

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Original Born densities inherit the exact matrix difference, in the low/high order. -/
theorem nearCriticalZero_bornDensity_difference
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (s : Ω) :
    M.bornDensity ρ s - M.bornDensity (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1) s =
      (M.bornDensity ρ s-M.bornDensity (calibratedHighState hd 0 ψ hN b hb0 hb1) s) -
        ((1-b)*ε)*(M.bornDensity ψ.state s-1) := by
  have he := congrArg (fun A => (A * M.traceDensity s).trace.re)
    (nearCriticalZeroHighState_difference hd ψ hN b hb0 hb1 ε hε0 hε1 ρ)
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_smul, Complex.sub_re, Complex.add_re,
    Complex.smul_re, smul_eq_mul] at he
  change M.bornDensity _ s-M.bornDensity ρ s =
    (M.bornDensity _ s-M.bornDensity ρ s) +
      ((1-b)*ε)*(M.bornDensity ψ.state s-M.bornDensity (quditMaximallyMixed d n) s) at he
  have hm : M.bornDensity (quditMaximallyMixed d n) s = 1 := M.bornDensity_maximallyMixed s
  rw [hm] at he
  linarith

theorem nearCriticalZero_referenceL2_sq
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (∫ s, (M.bornDensity ρ s-
      M.bornDensity (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1) s)^2 ∂M.traceReference) ≤
      2*(∫ s, (M.bornDensity ρ s-M.bornDensity (calibratedHighState hd 0 ψ hN b hb0 hb1) s)^2 ∂M.traceReference) +
        2*((1-b)*ε)^2*(∫ s, (M.bornDensity ψ.state s-1)^2 ∂M.traceReference) := by
  let H₀ := calibratedHighState hd 0 ψ hN b hb0 hb1
  have heq : (∫ s, (M.bornDensity ρ s-
      M.bornDensity (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1) s)^2 ∂M.traceReference) =
      ∫ s, (1*(M.bornDensity ρ s-M.bornDensity H₀ s) +
        (-((1-b)*ε))*(M.bornDensity ψ.state s-M.bornDensity (quditMaximallyMixed d n) s))^2 ∂M.traceReference := by
    apply integral_congr_ae
    apply ae_of_all
    intro s
    dsimp only
    rw [M.nearCriticalZero_bornDensity_difference, show
      M.bornDensity (quditMaximallyMixed d n) s = 1 from M.bornDensity_maximallyMixed s]
    dsimp only [H₀]
    ring
  rw [heq]
  simpa only [one_pow, mul_one, neg_sq, Pi.sub_apply,
    show M.bornDensity (quditMaximallyMixed d n) = fun _ => 1 from
      funext (M.bornDensity_maximallyMixed)] using
    Information.ReferenceL2.integral_square_combination_le M.traceReference
      (M.bornDensity ρ-M.bornDensity H₀) (M.bornDensity ψ.state-M.bornDensity (quditMaximallyMixed d n))
      ((M.bornDensity_memLp ρ).sub (M.bornDensity_memLp H₀))
      ((M.bornDensity_memLp ψ.state).sub (M.bornDensity_memLp (quditMaximallyMixed d n))) 1 (-((1-b)*ε))

/-- The physical degree-zero ordered information bound, before inserting the
two common-event quadratic estimates. -/
theorem nearCriticalZero_born_klDiv
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd 0 ψ hN < b)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2) :
    klDiv (M.born (calibratedLowState hd 0 ψ hN b hb0 hb1 hlb))
      (M.born (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1)) ≤
      ENNReal.ofReal ((4/(1-(b+(1-b)*((d : ℝ)+1)⁻¹))) *
        ((∫ s, (M.bornDensity (calibratedLowState hd 0 ψ hN b hb0 hb1 hlb) s-
          M.bornDensity (calibratedHighState hd 0 ψ hN b hb0 hb1) s)^2 ∂M.traceReference) +
          ((1-b)*ε)^2 * (∫ s, (M.bornDensity ψ.state s-1)^2 ∂M.traceReference))) := by
  let h := b+(1-b)*((d : ℝ)+1)⁻¹
  have hh : h < 1 := (zeroHighCoefficient_bounds (qudit_parameter_gt_one hd) hb0 hb1).2
  have hβ : 0 < (1-h)/2 := by linarith
  let L := calibratedLowState hd 0 ψ hN b hb0 hb1 hlb
  have hKL := M.born_klDiv_le_reference_sq L
    (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1) ((1-h)/2) hβ
    (nearCriticalZeroHighState_floor hd ψ hN b hb0 hb1 ε hε0 hε1)
  refine hKL.trans (ENNReal.ofReal_le_ofReal ?_)
  have hbnd := mul_le_mul_of_nonneg_left
    (M.nearCriticalZero_referenceL2_sq hd ψ hN b hb0 hb1 ε hε0 hε1 L) (inv_nonneg.mpr hβ.le)
  dsimp only [h, L] at hbnd ⊢
  rw [inv_div] at hbnd ⊢
  convert hbnd using 1; ring

end MeasurablePOVM

end LocalCertification.Quantum
