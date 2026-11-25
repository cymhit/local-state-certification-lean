import LocalCertification.Quantum.MeasurablePOVMCalibration
import LocalCertification.Extremal.DegreeHierarchy

/-! The actual adjacent-order mixtures in SM V.C.  Both degrees use the same
target and calibration level.  The high states are mixed with high states,
and the low states with low states; only degree j selects the KL ordering.
The quantitative information theorem takes two actual reference quadratic
bounds as inputs.  Establishing their common target event is separate. -/

set_option autoImplicit false
open MeasureTheory Matrix InformationTheory
open scoped ENNReal ComplexOrder
noncomputable section

namespace LocalCertification.Quantum.NearCriticalAdjacent

def gap (d j : ℕ) : ℝ := Extremal.gamma ((d:ℝ)+1) (j-1) - Extremal.gamma ((d:ℝ)+1) j

def weight (d j : ℕ) (ε : ℝ) : ℝ := ε / gap d j

theorem gap_pos {d : ℕ} (hd : 2 ≤ d) (j : ℕ) (hj : 1 ≤ j) : 0 < gap d j := by
  apply sub_pos.mpr
  exact Extremal.gamma_strictAnti ((d:ℝ)+1) (by exact_mod_cast (show 1 < d+1 by omega))
    (show j-1 < j by omega)

theorem weight_bounds {d : ℕ} (hd : 2 ≤ d) (j : ℕ) (hj : 1 ≤ j)
    (η : ℝ) (hη : η < gap d j / 2) (ε : ℝ) (hε : 0 < ε) (hεη : ε ≤ η) :
    0 < weight d j ε ∧ weight d j ε < 1/2 := by
  have hg := gap_pos hd j hj
  refine ⟨div_pos hε hg, (div_lt_iff₀ hg).mpr ?_⟩
  linarith

variable {d n : ℕ} [NeZero d]
  (hd : 2 ≤ d) (j : ℕ) (hj : 1 ≤ j)
  (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
  (hNj : (quditDualCertificate hd j).maxNode ≤ n)
  (hNp : (quditDualCertificate hd (j-1)).maxNode ≤ n)
  (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
  (hlj : uncalibratedLowFidelity hd j ψ hNj < b)
  (hlp : uncalibratedLowFidelity hd (j-1) ψ hNp < b)
  (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)

def high : QIT.State (CertificationGaussian.QuditIndex d n) :=
  binaryMixture (calibratedHighState hd j ψ hNj b hb0 hb1)
    (calibratedHighState hd (j-1) ψ hNp b hb0 hb1) t ht0 ht1

def low : QIT.State (CertificationGaussian.QuditIndex d n) :=
  binaryMixture (calibratedLowState hd j ψ hNj b hb0 hb1 hlj)
    (calibratedLowState hd (j-1) ψ hNp b hb0 hb1 hlp) t ht0 ht1

def numerator : QIT.State (CertificationGaussian.QuditIndex d n) :=
  if Even j then low hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1
  else high hd j ψ hNj hNp b hb0 hb1 t ht0 ht1

def denominator : QIT.State (CertificationGaussian.QuditIndex d n) :=
  if Even j then high hd j ψ hNj hNp b hb0 hb1 t ht0 ht1
  else low hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1

theorem low_fidelity :
    pureTargetFidelity ψ (low hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1) = b := by
  rw [low, binaryMixture_fidelity, calibratedLowState_fidelity, calibratedLowState_fidelity]
  ring

include hj in
theorem high_fidelity (ε : ℝ)
    (hε0 : 0 ≤ weight d j ε) (hε1 : weight d j ε ≤ 1) :
    b+(1-b)*(Extremal.gamma ((d:ℝ)+1) j+ε) ≤
      pureTargetFidelity ψ (high hd j ψ hNj hNp b hb0 hb1 (weight d j ε) hε0 hε1) := by
  rw [high, binaryMixture_fidelity]
  have h0 := mul_le_mul_of_nonneg_left (calibratedHighState_fidelity hd j ψ hNj b hb0 hb1)
    (sub_nonneg.mpr hε1)
  have h1 := mul_le_mul_of_nonneg_left (calibratedHighState_fidelity hd (j-1) ψ hNp b hb0 hb1) hε0
  have ht : weight d j ε * gap d j = ε := div_mul_cancel₀ ε (ne_of_gt (gap_pos hd j hj))
  dsimp only [gap] at ht
  nlinarith

theorem nonpositive_promise (ε : ℝ) (hε : ε ≤ 0) :
    pureTargetFidelity ψ (calibratedLowState hd j ψ hNj b hb0 hb1 hlj) = b ∧
    b+(1-b)*(Extremal.gamma ((d:ℝ)+1) j+ε) ≤
      pureTargetFidelity ψ (calibratedHighState hd j ψ hNj b hb0 hb1) := by
  refine ⟨calibratedLowState_fidelity hd j ψ hNj b hb0 hb1 hlj, ?_⟩
  have h := calibratedHighState_fidelity hd j ψ hNj b hb0 hb1
  have he := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hb1.le) hε
  nlinarith

/-- The second component follows the degree-j choice, not the degree-(j-1) choice. -/
theorem denominator_eq_mixture :
    denominator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1 =
      binaryMixture (calibratedDenominatorState hd j ψ hNj b hb0 hb1 hlj)
        (if Even j then calibratedHighState hd (j-1) ψ hNp b hb0 hb1
         else calibratedLowState hd (j-1) ψ hNp b hb0 hb1 hlp) t ht0 ht1 := by
  unfold denominator calibratedDenominatorState
  split_ifs <;> rfl

theorem denominator_floor :
    ((denominator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1).matrix -
      ((1-t)*calibratedUniformWeight hd j b) •
        (QIT.State.maximallyMixed (CertificationGaussian.QuditIndex d n)).matrix).PosSemidef := by
  rw [denominator_eq_mixture]
  exact binaryMixture_floor _ _ _ t _ ht0 ht1
    (MeasurablePOVM.calibrated_denominator_floor hd j ψ hNj b hb0 hb1 hlj)

omit [NeZero d] in
include hb1 in
theorem retained_background_ge_half (hthalf : t ≤ 1/2) :
    calibratedUniformWeight hd j b / 2 ≤ (1-t)*calibratedUniformWeight hd j b := by
  have hβ := calibratedUniformWeight_pos hd j hb1
  nlinarith

theorem denominator_half_floor (hthalf : t ≤ 1/2) :
    ((denominator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1).matrix -
      (calibratedUniformWeight hd j b / 2) •
        (QIT.State.maximallyMixed (CertificationGaussian.QuditIndex d n)).matrix).PosSemidef := by
  have h := (denominator_floor hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1).add
    ((QIT.State.maximallyMixed (CertificationGaussian.QuditIndex d n)).pos.smul
      (sub_nonneg.mpr (retained_background_ge_half hd j b hb1 t hthalf)))
  convert h using 1
  rw [sub_smul]
  abel

variable {Ω : Type*} [MeasurableSpace Ω]
  (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n))

theorem referenceL2_le :
    Real.sqrt (∫ s, (M.bornDensity (high hd j ψ hNj hNp b hb0 hb1 t ht0 ht1) s -
      M.bornDensity (low hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1) s)^2 ∂M.traceReference) ≤
    (1-t)*Real.sqrt (∫ s, (M.bornDensity (calibratedHighState hd j ψ hNj b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd j ψ hNj b hb0 hb1 hlj) s)^2 ∂M.traceReference) +
    t*Real.sqrt (∫ s, (M.bornDensity (calibratedHighState hd (j-1) ψ hNp b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd (j-1) ψ hNp b hb0 hb1 hlp) s)^2 ∂M.traceReference) :=
  M.referenceL2_binaryMixture_le _ _ _ _ t ht0 ht1

theorem referenceL2_sq_le :
    (∫ s, (M.bornDensity (high hd j ψ hNj hNp b hb0 hb1 t ht0 ht1) s -
      M.bornDensity (low hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1) s)^2 ∂M.traceReference) ≤
    2*(∫ s, (M.bornDensity (calibratedHighState hd j ψ hNj b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd j ψ hNj b hb0 hb1 hlj) s)^2 ∂M.traceReference) +
    2*t^2*(∫ s, (M.bornDensity (calibratedHighState hd (j-1) ψ hNp b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd (j-1) ψ hNp b hb0 hb1 hlp) s)^2 ∂M.traceReference) := by
  refine (M.referenceL2_sq_binaryMixture_le _ _ _ _ t ht0 ht1).trans ?_
  have hJ : 0 ≤ ∫ s, (M.bornDensity (calibratedHighState hd j ψ hNj b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd j ψ hNj b hb0 hb1 hlj) s)^2 ∂M.traceReference :=
    integral_nonneg fun _ => sq_nonneg _
  have hs : (1-t)^2 ≤ 1 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hs hJ
  nlinarith

theorem ordered_referenceL2_sq_eq :
    (∫ s, (M.bornDensity (numerator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1) s -
      M.bornDensity (denominator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1) s)^2 ∂M.traceReference) =
    ∫ s, (M.bornDensity (high hd j ψ hNj hNp b hb0 hb1 t ht0 ht1) s -
      M.bornDensity (low hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1) s)^2 ∂M.traceReference := by
  unfold numerator denominator
  split_ifs
  · apply integral_congr_ae
    exact ae_of_all _ fun s => by ring
  · rfl

theorem born_klDiv_le (hthalf : t ≤ 1/2) :
    klDiv (M.born (numerator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1))
      (M.born (denominator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1)) ≤
      ENNReal.ofReal ((4 / calibratedUniformWeight hd j b) *
        ((∫ s, (M.bornDensity (calibratedHighState hd j ψ hNj b hb0 hb1) s -
          M.bornDensity (calibratedLowState hd j ψ hNj b hb0 hb1 hlj) s)^2 ∂M.traceReference) +
         t^2 * (∫ s, (M.bornDensity (calibratedHighState hd (j-1) ψ hNp b hb0 hb1) s -
          M.bornDensity (calibratedLowState hd (j-1) ψ hNp b hb0 hb1 hlp) s)^2 ∂M.traceReference))) := by
  have hβ := calibratedUniformWeight_pos hd j hb1
  have h := M.born_klDiv_le_reference_sq
    (numerator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1)
    (denominator hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1) (calibratedUniformWeight hd j b/2)
    (by positivity) (denominator_half_floor hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1 hthalf)
  rw [ordered_referenceL2_sq_eq] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hbound := mul_le_mul_of_nonneg_left
    (referenceL2_sq_le hd j ψ hNj hNp b hb0 hb1 hlj hlp t ht0 ht1 M)
    (show 0 ≤ (calibratedUniformWeight hd j b/2)⁻¹ by positivity)
  convert hbound using 1
  field_simp
  ring

omit [NeZero d] in
def rateConstant (Cj Cp : ℝ) : ℝ :=
  (4 / calibratedUniformWeight hd j b) * max Cj (Cp/(gap d j)^2)

omit [NeZero d] in
include hb1 in
theorem rateConstant_pos (Cj Cp : ℝ) (hCj : 0 < Cj) : 0 < rateConstant hd j b Cj Cp := by
  exact mul_pos (div_pos (by norm_num) (calibratedUniformWeight_pos hd j hb1))
    (lt_of_lt_of_le hCj (le_max_left _ _))

/-- The constants precede epsilon and n.  The hypotheses are bounds on the
two actual calibrated-pair integrals for this very same POVM, not an assumed
bound on the new pair or an asserted concentration event. -/
theorem born_klDiv_le_rate (ε : ℝ) (hε0 : 0 ≤ weight d j ε) (hε1 : weight d j ε ≤ 1)
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n))
    (hthalf : weight d j ε ≤ 1/2) (Cj Cp : ℝ)
    (hJ : (∫ s, (M.bornDensity (calibratedHighState hd j ψ hNj b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd j ψ hNj b hb0 hb1 hlj) s)^2 ∂M.traceReference) ≤ Cj/(n:ℝ)^(j+1))
    (hP : (∫ s, (M.bornDensity (calibratedHighState hd (j-1) ψ hNp b hb0 hb1) s -
      M.bornDensity (calibratedLowState hd (j-1) ψ hNp b hb0 hb1 hlp) s)^2 ∂M.traceReference) ≤ Cp/(n:ℝ)^j) :
    klDiv (M.born (numerator hd j ψ hNj hNp b hb0 hb1 hlj hlp (weight d j ε) hε0 hε1))
      (M.born (denominator hd j ψ hNj hNp b hb0 hb1 hlj hlp (weight d j ε) hε0 hε1)) ≤
      ENNReal.ofReal (rateConstant hd j b Cj Cp * (1/(n:ℝ)^(j+1) + ε^2/(n:ℝ)^j)) := by
  refine (born_klDiv_le hd j ψ hNj hNp b hb0 hb1 hlj hlp (weight d j ε) hε0 hε1 M hthalf).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hβ := calibratedUniformWeight_pos hd j hb1
  have hA := add_le_add hJ (mul_le_mul_of_nonneg_left hP (sq_nonneg (weight d j ε)))
  have hB : Cj/(n:ℝ)^(j+1) ≤ max Cj (Cp/(gap d j)^2) / (n:ℝ)^(j+1) :=
    div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have hC : (weight d j ε)^2 * (Cp/(n:ℝ)^j) ≤
      max Cj (Cp/(gap d j)^2) * (ε^2/(n:ℝ)^j) := by
    calc
      _ = (Cp/(gap d j)^2) * (ε^2/(n:ℝ)^j) := by
        simp only [weight, div_eq_mul_inv, mul_pow, inv_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hD := hA.trans (add_le_add hB hC)
  have hE := mul_le_mul_of_nonneg_left hD (show 0 ≤ 4 / calibratedUniformWeight hd j b by positivity)
  convert hE using 1
  dsimp only [rateConstant]
  ring

end LocalCertification.Quantum.NearCriticalAdjacent
