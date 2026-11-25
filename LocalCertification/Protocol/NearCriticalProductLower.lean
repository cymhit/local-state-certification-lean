import LocalCertification.Quantum.NearCriticalAdjacentStates
import LocalCertification.Protocol.MeasurableProductLowerBound

/-! Actual positive-degree nearcritical hard pairs and general product-budget
lower bounds. Inputs are the two original calibrated-pair reference-square
bounds on the same target; their common probability event is separate. -/
set_option autoImplicit false
open MeasureTheory InformationTheory LocalCertification.Quantum CertificationGaussian
open LocalCertification.Extremal
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

theorem adjacent_states_nonpositive {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (j : ℕ)
    (ψ : QIT.PureVector (QuditIndex d n))
    (hNj : (quditDualCertificate hd j).maxNode ≤ n)
    (hNp : (quditDualCertificate hd (j-1)).maxNode ≤ n)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlj : uncalibratedLowFidelity hd j ψ hNj < b)
    (hlp : uncalibratedLowFidelity hd (j-1) ψ hNp < b)
    (ε : ℝ) (hε : ε ≤ 0)
    (ht0 : 0 ≤ NearCriticalAdjacent.weight d j (max ε 0))
    (ht1 : NearCriticalAdjacent.weight d j (max ε 0) ≤ 1) :
    NearCriticalAdjacent.high hd j ψ hNj hNp b hb0 hb1
      (NearCriticalAdjacent.weight d j (max ε 0)) ht0 ht1 = calibratedHighState hd j ψ hNj b hb0 hb1 ∧
    NearCriticalAdjacent.low hd j ψ hNj hNp b hb0 hb1 hlj hlp
      (NearCriticalAdjacent.weight d j (max ε 0)) ht0 ht1 = calibratedLowState hd j ψ hNj b hb0 hb1 hlj := by
  have ht : NearCriticalAdjacent.weight d j (max ε 0) = 0 := by
    change max ε 0 / NearCriticalAdjacent.gap d j = 0
    rw [max_eq_right hε, zero_div]
  constructor
  · apply QIT.State.ext
    change (1-NearCriticalAdjacent.weight d j (max ε 0)) •
        (calibratedHighState hd j ψ hNj b hb0 hb1).matrix +
      NearCriticalAdjacent.weight d j (max ε 0) •
        (calibratedHighState hd (j-1) ψ hNp b hb0 hb1).matrix = _
    rw [ht, sub_zero, one_smul, zero_smul, add_zero]
  · apply QIT.State.ext
    change (1-NearCriticalAdjacent.weight d j (max ε 0)) •
        (calibratedLowState hd j ψ hNj b hb0 hb1 hlj).matrix +
      NearCriticalAdjacent.weight d j (max ε 0) •
        (calibratedLowState hd (j-1) ψ hNp b hb0 hb1 hlp).matrix = _
    rw [ht, sub_zero, one_smul, zero_smul, add_zero]

theorem nearCritical_product_lower {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (j : ℕ) (hj : 1 ≤ j) (hn : 1 ≤ n)
    (ψ : QIT.PureVector (QuditIndex d n))
    (hNj : (quditDualCertificate hd j).maxNode ≤ n)
    (hNp : (quditDualCertificate hd (j-1)).maxNode ≤ n)
    (b η : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1)))
    (hlj : uncalibratedLowFidelity hd j ψ hNj < b)
    (hlp : uncalibratedLowFidelity hd (j-1) ψ hNp < b)
    (Cj Cp : ℝ) (hCj : 0 < Cj)
    (hJ : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd j ψ hNj b hb0 hb1) s -
        (MeasurablePOVM.product M).bornDensity (calibratedLowState hd j ψ hNj b hb0 hb1 hlj) s)^2
        ∂(MeasurablePOVM.product M).traceReference) ≤ Cj/(n : ℝ)^(j+1))
    (hP : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd (j-1) ψ hNp b hb0 hb1) s -
        (MeasurablePOVM.product M).bornDensity (calibratedLowState hd (j-1) ψ hNp b hb0 hb1 hlp) s)^2
        ∂(MeasurablePOVM.product M).traceReference) ≤ Cp/(n : ℝ)^j) :
    let C := NearCriticalAdjacent.rateConstant hd j b Cj Cp
    0 < C ∧ ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) /
        ENNReal.ofReal (C * (1/(n : ℝ)^(j+1) + (max ε 0)^2/(n : ℝ)^j)) ≤
          ProductBudget.expectedBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ∧
      ProductBudget.expectedBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ≤
        ENat.toENNReal (ProductBudget.maximumBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) := by
  let C := NearCriticalAdjacent.rateConstant hd j b Cj Cp
  have hC : 0 < C := NearCriticalAdjacent.rateConstant_pos hd j b hb1 Cj Cp hCj
  refine ⟨hC, ?_⟩
  intro ε _ hεη δ hδ hhalf
  have hg := NearCriticalAdjacent.gap_pos hd j hj
  have hηgap : η < NearCriticalAdjacent.gap d j / 2 := by
    have h := hwindow.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0:ℝ) ≤ 1/2))
    rw [ite_eq_right (show j ≠ 0 by omega)] at h
    change η < (gamma ((d:ℝ)+1) (j-1)-gamma ((d:ℝ)+1) j)/2
    linarith
  let e := max ε 0
  have he0 : 0 ≤ e := le_max_right _ _
  have heη : e ≤ η := max_le hεη hη.le
  have ht0 : 0 ≤ NearCriticalAdjacent.weight d j e := div_nonneg he0 hg.le
  have hthalf : NearCriticalAdjacent.weight d j e ≤ 1/2 := by
    apply (div_le_iff₀ hg).mpr
    linarith
  have ht1 : NearCriticalAdjacent.weight d j e ≤ 1 := hthalf.trans (by norm_num)
  let H := NearCriticalAdjacent.high hd j ψ hNj hNp b hb0 hb1 (NearCriticalAdjacent.weight d j e) ht0 ht1
  let L := NearCriticalAdjacent.low hd j ψ hNj hNp b hb0 hb1 hlj hlp (NearCriticalAdjacent.weight d j e) ht0 ht1
  have hhigh : b+(1-b)*(gamma ((d:ℝ)+1) j+ε) ≤ pureTargetFidelity ψ H := by
    have hf := NearCriticalAdjacent.high_fidelity hd j hj ψ hNj hNp b hb0 hb1 e ht0 ht1
    have hm := mul_le_mul_of_nonneg_left (le_max_left ε 0) (sub_nonneg.mpr hb1.le)
    change b+(1-b)*(gamma ((d:ℝ)+1) j+e) ≤ pureTargetFidelity ψ H at hf
    dsimp only [e] at hf
    linarith
  have hlow : pureTargetFidelity ψ L ≤ b :=
    (NearCriticalAdjacent.low_fidelity hd j ψ hNj hNp b hb0 hb1 hlj hlp _ ht0 ht1).le
  let Γ := C * (1/(n : ℝ)^(j+1) + e^2/(n : ℝ)^j)
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hΓ : 0 < Γ := mul_pos hC (add_pos_of_pos_of_nonneg
    (one_div_pos.mpr (pow_pos hnR _)) (div_nonneg (sq_nonneg _) (pow_nonneg hnR.le _)))
  have hInfo (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) :
      klDiv ((MeasurablePOVM.product M).born (if Even j then L else H))
        ((MeasurablePOVM.product M).born (if Even j then H else L)) ≤ ENNReal.ofReal Γ := by
    exact NearCriticalAdjacent.born_klDiv_le_rate hd j ψ hNj hNp b hb0 hb1 hlj hlp
      e ht0 ht1 (MeasurablePOVM.product M) hthalf Cj Cp (hJ Ω M) (hP Ω M)
  by_cases hjEven : Even j
  · apply ProductBudget.budget_bounds_low_high ψ _ b δ hδ hhalf L H hlow hhigh Γ hΓ
    intro Ω mΩ M
    have h := hInfo Ω M
    rw [ite_eq_left hjEven, ite_eq_left hjEven] at h
    exact h
  · apply ProductBudget.budget_bounds_high_low ψ _ b δ hδ hhalf H L hhigh hlow Γ hΓ
    intro Ω mΩ M
    have h := hInfo Ω M
    rw [ite_eq_right hjEven, ite_eq_right hjEven] at h
    exact h

end LocalCertification.Protocol.MeasurableExecution
