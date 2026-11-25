import LocalCertification.Quantum.BinaryStateMixture
import LocalCertification.Quantum.CalibratedInformation

/-! The existing calibrated physical states tested by an arbitrary measurable
POVM.  Calibration error and the ordered information bound are proved directly
for the actual normalized trace densities. -/

set_option autoImplicit false
open MeasureTheory Matrix InformationTheory
open scoped ENNReal ComplexOrder
noncomputable section

namespace LocalCertification.Quantum.MeasurablePOVM

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Nonempty I]

/-- A dimension bound for actual density differences, using normalization as
well as pointwise bounds.  No finite outcome alphabet is needed. -/
theorem referenceL2_sq_le_two_dimension (M : MeasurablePOVM Ω I) (ρ σ : QIT.State I) :
    (∫ s, (M.bornDensity ρ s - M.bornDensity σ s)^2 ∂M.traceReference) ≤
      2*(Fintype.card I : ℝ) := by
  have hpoint (s : Ω) : (M.bornDensity ρ s - M.bornDensity σ s)^2 ≤
      (Fintype.card I : ℝ) * (M.bornDensity ρ s + M.bornDensity σ s) := by
    have hf := M.bornDensity_nonneg ρ s
    have hg := M.bornDensity_nonneg σ s
    have hb := mul_nonneg hf (sub_nonneg.mpr (M.bornDensity_le ρ s))
    have hc := mul_nonneg hg (sub_nonneg.mpr (M.bornDensity_le σ s))
    nlinarith [mul_nonneg hf hg]
  have hi := ((M.bornDensity_memLp ρ).sub (M.bornDensity_memLp σ)).integrable_sq
  have hj := ((M.bornDensity_integrable ρ).add (M.bornDensity_integrable σ)).const_mul
    (Fintype.card I : ℝ)
  have h := integral_mono hi hj hpoint
  simp only [Pi.sub_apply, Pi.add_apply, integral_const_mul,
    integral_add (M.bornDensity_integrable ρ) (M.bornDensity_integrable σ),
    M.integral_bornDensity] at h
  linarith

theorem bornDensity_targetMixture (M : MeasurablePOVM Ω I) (ψ : QIT.PureVector I)
    (ρ : QIT.State I) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : Ω) :
    M.bornDensity (targetMixture ψ ρ t ht0 ht1) s =
      t * M.bornDensity ψ.state s + (1-t) * M.bornDensity ρ s := by
  simp only [bornDensity, targetMixture, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]

variable {d n : ℕ} [NeZero d]

/-- The exact calibrated difference for every original outcome label. -/
theorem calibrated_bornDensity_difference
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b) (s : Ω) :
    M.bornDensity (calibratedHighState hd r ψ hN b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s =
      (1-b) * (M.bornDensity (dualHighState hd (quditDualCertificate hd r) ψ hN) s -
        M.bornDensity (dualLowState hd (quditDualCertificate hd r) ψ hN) s) +
      (b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)) *
        (M.bornDensity ψ.state s - M.bornDensity (dualLowState hd (quditDualCertificate hd r) ψ hN) s) := by
  unfold calibratedHighState calibratedLowState
  rw [M.bornDensity_targetMixture, M.bornDensity_targetMixture]
  ring

/-- Minkowski's inequality separates the residual and the calibration correction
with their original coefficients on the common trace reference. -/
theorem calibrated_referenceL2
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    Real.sqrt (∫ s, (M.bornDensity (calibratedHighState hd r ψ hN b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s)^2 ∂M.traceReference) ≤
      (1-b) * Real.sqrt (∫ s,
        (M.bornDensity (dualHighState hd (quditDualCertificate hd r) ψ hN) s -
         M.bornDensity (dualLowState hd (quditDualCertificate hd r) ψ hN) s)^2 ∂M.traceReference) +
      (b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)) * Real.sqrt (2*(d:ℝ)^n) := by
  let H := dualHighState hd (quditDualCertificate hd r) ψ hN
  let L := dualLowState hd (quditDualCertificate hd r) ψ hN
  let e := b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)
  have he : 0 ≤ e := (calibrated_error_bounds hd r ψ hN b hb0 hb1 hlb).1
  simp_rw [M.calibrated_bornDensity_difference hd r ψ hN b hb0 hb1 hlb]
  have h := Information.ReferenceL2.sqrt_integral_square_combination_le M.traceReference
    (M.bornDensity H-M.bornDensity L) (M.bornDensity ψ.state-M.bornDensity L)
    ((M.bornDensity_memLp H).sub (M.bornDensity_memLp L))
    ((M.bornDensity_memLp ψ.state).sub (M.bornDensity_memLp L)) (1-b) e
  simp only [Pi.sub_apply, abs_of_nonneg he, abs_of_nonneg (sub_nonneg.mpr hb1.le)] at h
  have hdim : (∫ s, (M.bornDensity ψ.state s - M.bornDensity L s)^2 ∂M.traceReference) ≤
      2*(d:ℝ)^n := by
    simpa only [qudit_card, Nat.cast_pow] using M.referenceL2_sq_le_two_dimension ψ.state L
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdim) he))

/-- Squared reference distance separates the actual dual residual from the
actual calibration correction, with only a dimension-linear error term. -/
theorem calibrated_referenceL2_sq
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    (∫ s, (M.bornDensity (calibratedHighState hd r ψ hN b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s)^2 ∂M.traceReference) ≤
      2*(1-b)^2 * (∫ s,
        (M.bornDensity (dualHighState hd (quditDualCertificate hd r) ψ hN) s -
         M.bornDensity (dualLowState hd (quditDualCertificate hd r) ψ hN) s)^2 ∂M.traceReference) +
        4*(d : ℝ)^n*(b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))^2 := by
  let H := dualHighState hd (quditDualCertificate hd r) ψ hN
  let L := dualLowState hd (quditDualCertificate hd r) ψ hN
  let e := b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN)
  have heq : (∫ s, (M.bornDensity (calibratedHighState hd r ψ hN b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s)^2 ∂M.traceReference) =
      ∫ s, ((1-b)*(M.bornDensity H s-M.bornDensity L s) +
        e*(M.bornDensity ψ.state s-M.bornDensity L s))^2 ∂M.traceReference := by
    apply integral_congr_ae
    exact ae_of_all _ fun s => congrArg (fun x : ℝ => x^2)
      (M.calibrated_bornDensity_difference hd r ψ hN b hb0 hb1 hlb s)
  rw [heq]
  have h := Information.ReferenceL2.integral_square_combination_le M.traceReference
    (M.bornDensity H-M.bornDensity L) (M.bornDensity ψ.state-M.bornDensity L)
    ((M.bornDensity_memLp H).sub (M.bornDensity_memLp L))
    ((M.bornDensity_memLp ψ.state).sub (M.bornDensity_memLp L)) (1-b) e
  have hdim : (∫ s, (M.bornDensity ψ.state s-M.bornDensity L s)^2 ∂M.traceReference) ≤
      2*(d : ℝ)^n := by
    simpa only [qudit_card, Nat.cast_pow] using M.referenceL2_sq_le_two_dimension ψ.state L
  have hbnd := mul_le_mul_of_nonneg_left hdim (show 0 ≤ 2*e^2 by positivity)
  change _ ≤ 2*(1-b)^2*(∫ s, (M.bornDensity H s-M.bornDensity L s)^2 ∂M.traceReference) +
    4*(d : ℝ)^n*e^2
  simp only [Pi.sub_apply] at h
  nlinarith [h, hbnd]

/-- The existing degree-parity choice is retained for arbitrary POVMs. -/
theorem calibrated_denominator_floor (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    ((calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb).matrix -
      calibratedUniformWeight hd r b • (QIT.State.maximallyMixed (CertificationGaussian.QuditIndex d n)).matrix).PosSemidef := by
  unfold calibratedDenominatorState
  split_ifs with hr
  · exact calibratedHighState_uniform_floor hd r ψ hN b hb0 hb1 hr
  · exact calibratedLowState_uniform_floor hd r ψ hN b hb0 hb1 hlb (Nat.not_even_iff_odd.mp hr)

/-- The ordered Pearson chi-square divergence of the calibrated Born laws,
written against the normalized trace reference. The denominator has a
strictly positive density by the calibrated operator floor. -/
def calibratedOrderedChiSquare
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b) : ℝ≥0∞ :=
  let f := M.bornDensity (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb)
  let g := M.bornDensity (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)
  ∫⁻ s, ENNReal.ofReal ((f s-g s)^2 / g s) ∂M.traceReference

/-- The calibrated floor bounds the square root of the actual ordered
chi-square divergence by the reference distance divided by the square root
of the retained maximally mixed weight. -/
theorem calibrated_chiSquare_norm_le
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    M.calibratedOrderedChiSquare hd r ψ hN b hb0 hb1 hlb ≠ ⊤ ∧
      Real.sqrt (M.calibratedOrderedChiSquare hd r ψ hN b hb0 hb1 hlb).toReal ≤
        (Real.sqrt (calibratedUniformWeight hd r b))⁻¹ *
        Real.sqrt (∫ s, (M.bornDensity (calibratedHighState hd r ψ hN b hb0 hb1) s -
          M.bornDensity (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s)^2 ∂M.traceReference) := by
  let ρ := calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb
  let σ := calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb
  let β := calibratedUniformWeight hd r b
  let f := M.bornDensity ρ
  let g := M.bornDensity σ
  let χ := M.calibratedOrderedChiSquare hd r ψ hN b hb0 hb1 hlb
  have hβ : 0 < β := calibratedUniformWeight_pos hd r hb1
  have hfloor (s) : β ≤ g s :=
    M.bornDensity_ge_of_floor σ β (calibrated_denominator_floor hd r ψ hN b hb0 hb1 hlb) s
  have hi : Integrable (fun s => (f s - g s)^2) M.traceReference :=
    ((M.bornDensity_memLp ρ).sub (M.bornDensity_memLp σ)).integrable_sq
  have hnn : 0 ≤ ∫ s, (f s-g s)^2 ∂M.traceReference := integral_nonneg fun _ => sq_nonneg _
  have bound : χ ≤ ENNReal.ofReal (β⁻¹ * ∫ s, (f s-g s)^2 ∂M.traceReference) := by
    change (∫⁻ s, ENNReal.ofReal ((f s-g s)^2 / g s) ∂M.traceReference) ≤ _
    calc
      _ ≤ ∫⁻ s, ENNReal.ofReal (β⁻¹ * (f s-g s)^2) ∂M.traceReference := by
        apply lintegral_mono
        intro s
        apply ENNReal.ofReal_le_ofReal
        simpa only [div_eq_mul_inv, mul_comm] using
          div_le_div_of_nonneg_left (sq_nonneg (f s-g s)) hβ (hfloor s)
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul β⁻¹)
          (ae_of_all _ (fun s => mul_nonneg (inv_nonneg.mpr hβ.le) (sq_nonneg _))), integral_const_mul]
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top bound, ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
  rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hβ.le) hnn)] at hr
  have h := Real.sqrt_le_sqrt hr
  rw [Real.sqrt_mul (inv_nonneg.mpr hβ.le), Real.sqrt_inv] at h
  have heq : (∫ s, (f s-g s)^2 ∂M.traceReference) =
      ∫ s, (M.bornDensity (calibratedHighState hd r ψ hN b hb0 hb1) s -
        M.bornDensity (calibratedLowState hd r ψ hN b hb0 hb1 hlb) s)^2 ∂M.traceReference := by
    dsimp only [f,g,ρ,σ,calibratedNumeratorState,calibratedDenominatorState]
    split_ifs
    · apply integral_congr_ae
      exact ae_of_all _ fun s => by ring
    · rfl
  rwa [heq] at h

/-- Ordered actual Born information for the same calibrated states, now for
every arbitrary measurable POVM.  A product common-event bound is a separate input. -/
theorem calibrated_born_klDiv
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b) :
    klDiv (M.born (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
      (M.born (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤
      ENNReal.ofReal ((calibratedUniformWeight hd r b)⁻¹ *
        (2*(1-b)^2 * (∫ s,
          (M.bornDensity (dualHighState hd (quditDualCertificate hd r) ψ hN) s -
           M.bornDensity (dualLowState hd (quditDualCertificate hd r) ψ hN) s)^2 ∂M.traceReference) +
          4*(d : ℝ)^n*(b-calibrationAlpha b (uncalibratedLowFidelity hd r ψ hN))^2)) := by
  have hβ := calibratedUniformWeight_pos hd r hb1
  let ρ := calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb
  let σ := calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb
  let χ := M.calibratedOrderedChiSquare hd r ψ hN b hb0 hb1 hlb
  have hkl : klDiv (M.born ρ) (M.born σ) ≤ χ :=
    Information.DensityInformation.klDiv_le_reference_chiSquare M.traceReference (M.born ρ) (M.born σ)
      (M.bornDensity ρ) (M.bornDensity σ) (M.bornDensity_measurable ρ) (M.bornDensity_measurable σ)
      (M.bornDensity_nonneg ρ) (fun s => hβ.trans_le (M.bornDensity_ge_of_floor σ _
        (calibrated_denominator_floor hd r ψ hN b hb0 hb1 hlb) s))
      (M.born_eq_withDensity ρ) (M.born_eq_withDensity σ)
  obtain ⟨hfin, hsqrt⟩ := M.calibrated_chiSquare_norm_le hd r ψ hN b hb0 hb1 hlb
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  rw [Real.sq_sqrt ENNReal.toReal_nonneg, mul_pow, inv_pow, Real.sq_sqrt hβ.le,
    Real.sq_sqrt (integral_nonneg (fun s => sq_nonneg _))] at hs
  refine hkl.trans ?_
  change χ ≤ _
  rw [← ENNReal.ofReal_toReal (show χ ≠ ⊤ from hfin)]
  exact ENNReal.ofReal_le_ofReal (hs.trans (mul_le_mul_of_nonneg_left
    (M.calibrated_referenceL2_sq hd r ψ hN b hb0 hb1 hlb) (inv_nonneg.mpr hβ.le)))

end LocalCertification.Quantum.MeasurablePOVM
