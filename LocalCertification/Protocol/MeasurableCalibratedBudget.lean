import LocalCertification.Protocol.MeasurableProductLowerBound
import LocalCertification.Quantum.CalibratedInformation

/-! Exact optimized budgets from the actual calibrated hard pair.

Parity fixes the order of the two physical states before any measurement is
chosen. The uniform original-product information bound is supplied by the
common target event; this consumer retains the exact testing factor and all
infinite-cost cases while optimizing over genuine measurable protocols.
-/

set_option autoImplicit false
open MeasureTheory InformationTheory LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u
variable {d n : Nat} [NeZero d]

theorem calibrated_budget_bounds (hd : 2≤d) (r : Nat)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode≤n) (a b δ : ℝ)
    (hb0 : 0<b) (hb1 : b<1) (hlb : uncalibratedLowFidelity hd r ψ hN<b)
    (hgap : (a-b)/(1-b)≤gamma ((d:ℝ)+1) r) (hδ : 0<δ) (hhalf : δ<1/2)
    (Γ : ℝ) (hΓ : 0<Γ)
    (hstep : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      klDiv ((MeasurablePOVM.product M).born (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
        ((MeasurablePOVM.product M).born (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤
          ENNReal.ofReal Γ) :
    ENNReal.ofReal (LocalCertification.Information.testingThreshold δ)/ENNReal.ofReal Γ ≤
      expectedBudget.{u} ψ a b δ ∧
      expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} ψ a b δ) := by
  have hp := calibrated_exact_window hd r ψ hN a b hb0 hb1 hlb hgap
  by_cases hr : Even r
  · have hnum : calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb =
        calibratedLowState hd r ψ hN b hb0 hb1 hlb := ite_eq_left hr
    have hden : calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb =
        calibratedHighState hd r ψ hN b hb0 hb1 := ite_eq_left hr
    apply budget_bounds_low_high ψ a b δ hδ hhalf
      (calibratedLowState hd r ψ hN b hb0 hb1 hlb)
      (calibratedHighState hd r ψ hN b hb0 hb1) hp.1.le hp.2 Γ hΓ
    intro Ω mΩ M
    have h := hstep Ω M
    rw [hnum,hden] at h
    exact h
  · have hnum : calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb =
        calibratedHighState hd r ψ hN b hb0 hb1 := ite_eq_right hr
    have hden : calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb =
        calibratedLowState hd r ψ hN b hb0 hb1 hlb := ite_eq_right hr
    apply budget_bounds_high_low ψ a b δ hδ hhalf
      (calibratedHighState hd r ψ hN b hb0 hb1)
      (calibratedLowState hd r ψ hN b hb0 hb1 hlb) hp.2 hp.1.le Γ hΓ
    intro Ω mΩ M
    have h := hstep Ω M
    rw [hnum,hden] at h
    exact h

/-- The same exact inequality in the power-law scale, with no confidence cutoff. -/
theorem calibrated_budget_power_bounds (hd : 2≤d) (r : Nat) (hn : 1≤n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (hN : (quditDualCertificate hd r).maxNode≤n) (a b δ : ℝ)
    (hb0 : 0<b) (hb1 : b<1) (hlb : uncalibratedLowFidelity hd r ψ hN<b)
    (hgap : (a-b)/(1-b)≤gamma ((d:ℝ)+1) r) (hδ : 0<δ) (hhalf : δ<1/2)
    (K : ℝ) (hK : 0<K)
    (hstep : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      klDiv ((MeasurablePOVM.product M).born (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
        ((MeasurablePOVM.product M).born (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤
          ENNReal.ofReal (K/(n:ℝ)^(r+1))) :
    ENNReal.ofReal ((LocalCertification.Information.testingThreshold δ/K)*(n:ℝ)^(r+1)) ≤
      expectedBudget.{u} ψ a b δ ∧
      expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} ψ a b δ) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hΓ : 0 < K/(n:ℝ)^(r+1) := by positivity
  have h := calibrated_budget_bounds hd r ψ hN a b δ hb0 hb1 hlb hgap hδ hhalf
    (K/(n:ℝ)^(r+1)) hΓ hstep
  have he : LocalCertification.Information.testingThreshold δ/(K/(n:ℝ)^(r+1)) =
      (LocalCertification.Information.testingThreshold δ/K)*(n:ℝ)^(r+1) := by
    field_simp [hK.ne', hn0.ne']
  rw [← ENNReal.ofReal_div_of_pos hΓ, he] at h
  exact h

end LocalCertification.Protocol.MeasurableExecution.ProductBudget
