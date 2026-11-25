import LocalCertification.Protocol.NearCriticalProductLower
import LocalCertification.Protocol.NearCriticalZeroProductLower
set_option autoImplicit false
open MeasureTheory LocalCertification.Quantum CertificationGaussian
open LocalCertification.Extremal
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

theorem nearCritical_rate_identity (L C ε : ℝ) (hC : 0 < C) (n j : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal L / ENNReal.ofReal (C * (1/(n : ℝ)^(j+1) + (max ε 0)^2/(n : ℝ)^j)) =
      ENNReal.ofReal ((L/C)*(n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < C * (1/(n : ℝ)^(j+1) + (max ε 0)^2/(n : ℝ)^j) :=
    mul_pos hC (add_pos_of_pos_of_nonneg (one_div_pos.mpr (pow_pos hnR _))
      (div_nonneg (sq_nonneg _) (pow_nonneg hnR.le _)))
  rw [← ENNReal.ofReal_div_of_pos hden]
  apply congrArg ENNReal.ofReal
  have hsum : 1/(n : ℝ)^(j+1) + (max ε 0)^2/(n : ℝ)^j =
      (1+(n : ℝ)*(max ε 0)^2)/(n : ℝ)^(j+1) := by
    rw [pow_succ]
    field_simp
  rw [hsum]
  field_simp

theorem nearCritical_product_lower_crossover {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (j : ℕ) (hj : 1 ≤ j) (hn : 1 ≤ n)
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
      ENNReal.ofReal ((LocalCertification.Information.testingThreshold δ / C) *
        (n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) ≤
          ProductBudget.expectedBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ∧
      ProductBudget.expectedBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ≤
        ENat.toENNReal (ProductBudget.maximumBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) := by
  have h := nearCritical_product_lower hd j hj hn ψ hNj hNp b η hb0 hb1 hη
    hwindow hlj hlp Cj Cp hCj hJ hP
  refine ⟨h.1, ?_⟩
  intro ε hεl hεu δ hδ hhalf
  have hb := h.2 ε hεl hεu δ hδ hhalf
  rw [nearCritical_rate_identity _ _ ε h.1 n j hn] at hb
  exact hb

theorem nearCritical_zero_product_lower_crossover {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (hn : 1 ≤ n)
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
      ENNReal.ofReal ((LocalCertification.Information.testingThreshold δ / C) *
        (n : ℝ)/(1+(n : ℝ)*(max ε 0)^2)) ≤
          ProductBudget.expectedBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) 0+ε)) b δ ∧
      ProductBudget.expectedBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) 0+ε)) b δ ≤
        ENat.toENNReal (ProductBudget.maximumBudget.{u} ψ (b+(1-b)*(gamma ((d : ℝ)+1) 0+ε)) b δ) := by
  have h := nearCritical_zero_product_lower hd hn ψ hN b η hb0 hb1 hη
    hwindow hlb C₀ Cₚ hC₀ hA hB
  refine ⟨h.1, ?_⟩
  intro ε hεl hεu δ hδ hhalf
  have hb := h.2 ε hεl hεu δ hδ hhalf
  have hid := nearCritical_rate_identity (LocalCertification.Information.testingThreshold δ)
    (zeroRateConstant d b C₀ Cₚ) ε h.1 n 0 hn
  rw [Nat.zero_add, pow_one, pow_zero, div_one] at hid
  rw [hid] at hb
  exact hb

end LocalCertification.Protocol.MeasurableExecution
