import LocalCertification.Quantum.NearCriticalZeroStates

/-! Explicit degree-zero transition constants.  The two input inequalities
are about the original pair and the pure-versus-mixed density for this same
POVM.  Their common target-event construction is a separate theorem. -/

set_option autoImplicit false
open MeasureTheory InformationTheory
open scoped ENNReal
noncomputable section

namespace LocalCertification.Quantum

/-- Independent of the target, system size, POVM and perturbation. -/
def zeroRateConstant (d : ℕ) (b C₀ Cₚ : ℝ) : ℝ :=
  (4/(1-(b+(1-b)*((d : ℝ)+1)⁻¹))) * max C₀ ((1-b)^2*Cₚ)

theorem zeroRateConstant_pos {d : ℕ} (hd : 2 ≤ d) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (C₀ Cₚ : ℝ) (hC₀ : 0 < C₀) : 0 < zeroRateConstant d b C₀ Cₚ := by
  have hh := (zeroHighCoefficient_bounds (qudit_parameter_gt_one hd) hb0 hb1).2
  exact mul_pos (div_pos (by norm_num) (sub_pos.mpr hh)) (hC₀.trans_le (le_max_left _ _))

namespace MeasurablePOVM

variable {Ω : Type*} [MeasurableSpace Ω] {d n : ℕ} [NeZero d]

theorem nearCriticalZero_born_klDiv_rate
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n)) (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd 0).maxNode ≤ n) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd 0 ψ hN < b)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (1-((d : ℝ)+1)⁻¹)/2) (C₀ Cₚ : ℝ)
    (hA : (∫ s, (M.bornDensity (calibratedLowState hd 0 ψ hN b hb0 hb1 hlb) s-
      M.bornDensity (calibratedHighState hd 0 ψ hN b hb0 hb1) s)^2 ∂M.traceReference) ≤ C₀/n)
    (hB : (∫ s, (M.bornDensity ψ.state s-1)^2 ∂M.traceReference) ≤ Cₚ) :
    klDiv (M.born (calibratedLowState hd 0 ψ hN b hb0 hb1 hlb))
      (M.born (nearCriticalZeroHighState hd ψ hN b hb0 hb1 ε hε0 hε1)) ≤
      ENNReal.ofReal (zeroRateConstant d b C₀ Cₚ * (1/(n : ℝ)+ε^2)) := by
  refine (M.nearCriticalZero_born_klDiv hd ψ hN b hb0 hb1 hlb ε hε0 hε1).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hh := (zeroHighCoefficient_bounds (qudit_parameter_gt_one hd) hb0 hb1).2
  have h₁ := add_le_add hA (mul_le_mul_of_nonneg_left hB (sq_nonneg ((1-b)*ε)))
  have h₂ : C₀/(n : ℝ) ≤ max C₀ ((1-b)^2*Cₚ)/(n : ℝ) :=
    div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  have h₃ : ((1-b)*ε)^2*Cₚ ≤ max C₀ ((1-b)^2*Cₚ)*ε^2 := by
    calc
      _ = ((1-b)^2*Cₚ)*ε^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  have h₄ := mul_le_mul_of_nonneg_left (h₁.trans (add_le_add h₂ h₃))
    (show 0 ≤ 4/(1-(b+(1-b)*((d : ℝ)+1)⁻¹)) by positivity)
  convert h₄ using 1
  dsimp only [zeroRateConstant]
  ring

end MeasurablePOVM
end LocalCertification.Quantum
