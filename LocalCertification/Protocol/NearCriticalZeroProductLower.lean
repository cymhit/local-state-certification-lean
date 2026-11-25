import LocalCertification.Quantum.NearCriticalZeroRate
import LocalCertification.Protocol.MeasurableProductLowerBound

/-! The actual degree-zero transition enters the full measurable-product
budget. Only original-POVM reference-square bounds are inputs; the common
target event remains a separate construction. -/
set_option autoImplicit false
open MeasureTheory LocalCertification.Quantum CertificationGaussian
open LocalCertification.Extremal
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

theorem zero_high_state_nonpositive {d n : ℕ} [NeZero d] (hd : 2 ≤ d)
    (ψ : QIT.PureVector (QuditIndex d n)) (hN : (quditDualCertificate hd 0).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (ε : ℝ) (hε : ε ≤ 0)
    (he0 : 0 ≤ max ε 0) (he1 : max ε 0 ≤ (1-((d : ℝ)+1)⁻¹)/2) :
    nearCriticalZeroHighState hd ψ hN b hb0 hb1 (max ε 0) he0 he1 =
      calibratedHighState hd 0 ψ hN b hb0 hb1 := by
  have ht : zeroMixingWeight ((d : ℝ)+1) (max ε 0) = 0 := by
    change max ε 0 / (1-((d : ℝ)+1)⁻¹) = 0
    rw [max_eq_right hε, zero_div]
  apply QIT.State.ext
  change (1-zeroMixingWeight ((d : ℝ)+1) (max ε 0)) •
      (calibratedHighState hd 0 ψ hN b hb0 hb1).matrix +
    zeroMixingWeight ((d : ℝ)+1) (max ε 0) • ψ.state.matrix = _
  rw [ht, sub_zero, one_smul, zero_smul, add_zero]

theorem nearCritical_zero_product_lower {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (ψ : QIT.PureVector (QuditIndex d n)) (hN : (quditDualCertificate hd 0).maxNode ≤ n)
    (b η : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min (1-gamma ((d : ℝ)+1) 0)
      (gamma ((d : ℝ)+1) 0-gamma ((d : ℝ)+1) 1))
    (hlb : uncalibratedLowFidelity hd 0 ψ hN < b) (C₀ Cₚ : ℝ) (hC₀ : 0 < C₀)
    (hA : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd 0 ψ hN b hb0 hb1) s -
        (MeasurablePOVM.product M).bornDensity (calibratedLowState hd 0 ψ hN b hb0 hb1 hlb) s)^2
        ∂(MeasurablePOVM.product M).traceReference) ≤ C₀/(n : ℝ))
    (hB : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      (∫ s, ((MeasurablePOVM.product M).bornDensity ψ.state s-1)^2
        ∂(MeasurablePOVM.product M).traceReference) ≤ Cₚ) :
    let C := zeroRateConstant d b C₀ Cₚ
    0 < C ∧ ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) /
        ENNReal.ofReal (C * (1/(n : ℝ) + (max ε 0)^2)) ≤
          ProductBudget.expectedBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) 0+ε)) b δ ∧
      ProductBudget.expectedBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) 0+ε)) b δ ≤
        ENat.toENNReal (ProductBudget.maximumBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) 0+ε)) b δ) := by
  let C := zeroRateConstant d b C₀ Cₚ
  have hC : 0 < C := zeroRateConstant_pos hd hb0 hb1 C₀ Cₚ hC₀
  refine ⟨hC, ?_⟩
  intro ε _ hεη δ hδ hhalf
  have hηgap : η < (1-((d : ℝ)+1)⁻¹)/2 := by
    have h := hwindow.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0:ℝ) ≤ 1/2))
    rw [gamma_zero _ (qudit_parameter_gt_one hd)] at h
    linarith
  let e := max ε 0
  have he0 : 0 ≤ e := le_max_right _ _
  have heη : e ≤ η := max_le hεη hη.le
  have he1 : e ≤ (1-((d : ℝ)+1)⁻¹)/2 := heη.trans hηgap.le
  let H := nearCriticalZeroHighState hd ψ hN b hb0 hb1 e he0 he1
  let L := calibratedLowState hd 0 ψ hN b hb0 hb1 hlb
  have hhigh : b+(1-b)*(gamma ((d:ℝ)+1) 0+ε) ≤ pureTargetFidelity ψ H := by
    rw [gamma_zero _ (qudit_parameter_gt_one hd)]
    have hf := nearCriticalZeroHighState_fidelity hd ψ hN b hb0 hb1 e he0 he1
    have hm := mul_le_mul_of_nonneg_left (le_max_left ε 0) (sub_nonneg.mpr hb1.le)
    change b+(1-b)*(((d:ℝ)+1)⁻¹+e) ≤ pureTargetFidelity ψ H at hf
    dsimp only [e] at hf
    linarith
  have hlow : pureTargetFidelity ψ L ≤ b := (calibratedLowState_fidelity hd 0 ψ hN b hb0 hb1 hlb).le
  let Γ := C * (1/(n : ℝ) + e^2)
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hΓ : 0 < Γ := mul_pos hC (add_pos_of_pos_of_nonneg (one_div_pos.mpr hnR) (sq_nonneg e))
  apply ProductBudget.budget_bounds_low_high ψ _ b δ hδ hhalf L H hlow hhigh Γ hΓ
  intro Ω mΩ M
  apply (MeasurablePOVM.product M).nearCriticalZero_born_klDiv_rate hd ψ hN b hb0 hb1 hlb e he0 he1 C₀ Cₚ
  · calc
      _ = ∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd 0 ψ hN b hb0 hb1) s -
          (MeasurablePOVM.product M).bornDensity (calibratedLowState hd 0 ψ hN b hb0 hb1 hlb) s)^2
          ∂(MeasurablePOVM.product M).traceReference := by
        apply integral_congr_ae
        exact ae_of_all _ fun _ => by ring
      _ ≤ _ := hA Ω M
  · exact hB Ω M

end LocalCertification.Protocol.MeasurableExecution
