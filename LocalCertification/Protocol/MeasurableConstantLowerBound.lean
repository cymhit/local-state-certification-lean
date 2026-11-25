import LocalCertification.Protocol.MeasurableProductLowerBound
import LocalCertification.Quantum.MeasurableConstantHardPair
import LocalCertification.Information.ConfidenceRange

/-! # Constant-order lower bounds for all measurable product protocols

The fixed hard pair is the target and its original target/uniform mixture.
Its information bound holds for every measurable POVM, hence for every allowed
local product. The optimized budgets below include arbitrary measurable
outcomes, adaptive settings, random stopping, and infinite expected costs.
The common dimension cutoff precedes every pure target, upper promise and
confidence level. These stronger bounds cover the degree-zero branch of the
tolerance hierarchy without a target exceptional set.
-/

set_option autoImplicit false
open MeasureTheory Filter LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u
variable {d n : ℕ} [NeZero d]

/-- The exact binary testing factor divided by the actual per-copy information
bound lower-bounds optimization over the entire product protocol class. -/
theorem constant_budget_bounds
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) (ha : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hD : ((d : ℝ)^n)⁻¹ ≤ b/2) (hδ : 0 < δ) (hhalf : δ < 1/2) :
    ENNReal.ofReal (testingThreshold δ) / ENNReal.ofReal (4/b+2) ≤
      expectedBudget.{u} ψ a b δ ∧
    expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} ψ a b δ) := by
  apply budget_bounds_high_low ψ a b δ hδ hhalf ψ.state
    (constantLowState ψ b hb0 hb1)
    (by rwa [pureTargetFidelity_self])
    (constantLowState_promised ψ b hb0 hb1 hD) (4/b+2) (by positivity)
  intro Ω _ M
  exact (MeasurablePOVM.product M).constantLowState_born_klDiv ψ b hb0 hb1

/-- One dimension threshold works simultaneously for every target and every
error level in the entire open interval `(0,1/2)`. -/
theorem constant_budget_bounds_eventually (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n),
      ∀ a : ℝ, a ≤ 1 → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ENNReal.ofReal (testingThreshold δ) / ENNReal.ofReal (4/b+2) ≤
        expectedBudget.{u} ψ a b δ ∧
      expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} ψ a b δ) := by
  have hd' : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have ht : Tendsto (fun n : ℕ => ((d : ℝ)^n)⁻¹) atTop (nhds 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ (d : ℝ)⁻¹ by positivity) (inv_lt_one_of_one_lt₀ hd')
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < b/2 by positivity))] with n hn
  intro ψ a ha δ hδ hhalf
  exact constant_budget_bounds ψ a b δ ha hb0 hb1 hn.le hδ hhalf

/-- Every fixed confidence cutoff strictly below one half gives a positive
logarithmic coefficient, for both optimized budgets and every pure target. -/
theorem constant_budget_confidence_eventually (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (δstar : ℝ) (hs0 : 0 < δstar) (hshalf : δstar < 1/2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n), ∀ a : ℝ, a ≤ 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
      ENNReal.ofReal (c*Real.log (1/δ)) ≤ expectedBudget.{u} ψ a b δ ∧
      expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} ψ a b δ) := by
  have hfac := confidenceFactor_pos δstar hs0 hshalf
  have hΓ : 0 < 4/b+2 := by positivity
  refine ⟨confidenceFactor δstar/(4/b+2), div_pos hfac hΓ, ?_⟩
  filter_upwards [constant_budget_bounds_eventually.{u} d hd b hb0 hb1] with n hn
  intro ψ a ha δ hδ hcut
  obtain ⟨hLower, hUpper⟩ := hn ψ a ha δ hδ (hcut.trans_lt hshalf)
  refine ⟨?_, hUpper⟩
  rw [← ENNReal.ofReal_div_of_pos hΓ] at hLower
  apply (ENNReal.ofReal_le_ofReal ?_).trans hLower
  calc
    (confidenceFactor δstar/(4/b+2))*Real.log (1/δ) =
        (confidenceFactor δstar*Real.log (1/δ))/(4/b+2) := by ring
    _ ≤ testingThreshold δ/(4/b+2) := div_le_div_of_nonneg_right
      (testingThreshold_confidence_lower δstar hs0 hshalf δ hδ hcut) hΓ.le

end LocalCertification.Protocol.MeasurableExecution.ProductBudget
