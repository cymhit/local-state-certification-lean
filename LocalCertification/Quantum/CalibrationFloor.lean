import LocalCertification.Quantum.Calibration

set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Quantum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Positive matrices have nonnegative readout in every actual rank-one basis effect. -/
theorem basis_effect_pairing_nonneg (A : Matrix I I ℂ) (hA : A.PosSemidef)
    (U : ↥(unitary (Matrix I I ℂ))) (x : I) :
    0 ≤ (A * (basisPOVM U).effects x).trace.re := by
  rw [basisPOVM_effect_rankOne]
  have h := hA.dotProduct_mulVec_nonneg (fun i => U.val i x)
  have he : (A * QIT.rankOneMatrix (fun i => U.val i x)).trace =
      (star (fun i => U.val i x)) ⬝ᵥ (A.mulVec (fun i => U.val i x)) := by
    simp only [QIT.rankOneMatrix, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    exact dotProduct_comm _ _
  rw [he]
  exact h.1

variable {d : ℕ} [NeZero d] {n : ℕ}

theorem basisBorn_quditMaximallyMixed
    (U : ↥(unitary (Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ)))
    (x : CertificationGaussian.QuditIndex d n) : basisBorn U (quditMaximallyMixed d n) x = ((d : ℝ)^n)⁻¹ := by
  rw [basisBorn_trace, quditMaximallyMixed_matrix, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, basisPOVM_effect_trace]
  simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]

/-- A genuine uniform PSD component gives a pointwise Born denominator for every basis. -/
theorem basisBorn_uniform_floor (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (κ : ℝ)
    (hρ : (ρ.matrix - κ • (quditMaximallyMixed d n).matrix).PosSemidef)
    (U : ↥(unitary (Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ)))
    (x : CertificationGaussian.QuditIndex d n) : κ / (d : ℝ)^n ≤ basisBorn U ρ x := by
  have h := basis_effect_pairing_nonneg _ hρ U x
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul] at h
  rw [← basisBorn_trace, ← basisBorn_trace, basisBorn_quditMaximallyMixed] at h
  simpa only [div_eq_mul_inv] using sub_nonneg.mp h

omit [NeZero d] in
/-- The denominator constant depends only on d,r,b and is independent of the target and n. -/
def calibratedUniformWeight (hd : 2 ≤ d) (r : ℕ) (b : ℝ) : ℝ :=
  (1-b)*uniformComponentWeight (quditDualCertificate hd r)

omit [NeZero d] in
theorem calibratedUniformWeight_pos (hd : 2 ≤ d) (r : ℕ) {b : ℝ} (hb1 : b < 1) :
    0 < calibratedUniformWeight hd r b :=
  mul_pos (sub_pos.mpr hb1) (uniformComponentWeight_pos (qudit_parameter_gt_one hd) _)

/-- The high state retains the required fixed uniform component for even degree. -/
theorem calibratedHighState_uniform_floor (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hr : Even r) :
    ((calibratedHighState hd r ψ hN b hb0 hb1).matrix -
      calibratedUniformWeight hd r b • (quditMaximallyMixed d n).matrix).PosSemidef :=
  targetMixture_floor ψ _ _ _ b hb0.le hb1.le
    (dualHighState_uniform_floor_even hd (quditDualCertificate hd r) ψ hN hr)

/-- The low state retains at least the same fixed component for odd degree, since alpha≤b. -/
theorem calibratedLowState_uniform_floor (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (hr : Odd r) :
    ((calibratedLowState hd r ψ hN b hb0 hb1 hlb).matrix -
      calibratedUniformWeight hd r b • (quditMaximallyMixed d n).matrix).PosSemidef := by
  let α := calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)
  let κ := uniformComponentWeight (quditDualCertificate hd r)
  have hα := calibrationAlpha_bounds (b := b) (l := uncalibratedLowFidelity hd r ψ hN) hb0 hb1 (pureTargetFidelity_nonneg ψ
    (dualLowState hd (quditDualCertificate hd r) ψ hN)) hlb
  have hκ : 0 < κ := uniformComponentWeight_pos (qudit_parameter_gt_one hd) _
  have hfloor := targetMixture_floor ψ (dualLowState hd (quditDualCertificate hd r) ψ hN)
    (quditMaximallyMixed d n) κ α hα.1 (hα.2.trans hb1.le)
    (dualLowState_uniform_floor_odd hd (quditDualCertificate hd r) ψ hN hr)
  have hcoef : 0 ≤ (1-α)*κ - (1-b)*κ := by dsimp only [α]; nlinarith [hα.2]
  have hpos := hfloor.add ((quditMaximallyMixed d n).pos.smul hcoef)
  convert hpos using 1
  dsimp only [calibratedLowState, calibratedUniformWeight, α, κ]
  rw [sub_smul]
  abel

/-- The fixed parity ordering always puts the uniform-containing state in the denominator. -/
def calibratedDenominatorState (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    QIT.State (CertificationGaussian.QuditIndex d n) :=
  if Even r then calibratedHighState hd r ψ hN b hb0 hb1 else calibratedLowState hd r ψ hN b hb0 hb1 hlb

theorem calibrated_productBorn_denominator (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    calibratedUniformWeight hd r b / (d : ℝ)^n ≤
      productBorn d n U (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb) x := by
  apply basisBorn_uniform_floor
  unfold calibratedDenominatorState
  split_ifs with hr
  · exact calibratedHighState_uniform_floor hd r ψ hN b hb0 hb1 hr
  · exact calibratedLowState_uniform_floor hd r ψ hN b hb0 hb1 hlb (Nat.not_even_iff_odd.mp hr)

end LocalCertification.Quantum
