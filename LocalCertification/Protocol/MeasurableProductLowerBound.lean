import LocalCertification.Protocol.MeasurableExecutionInformation
import LocalCertification.Protocol.MeasurableExecutionBudgets

/-! A uniform information bound for a fixed actual hard pair implies a lower
bound on optimization over all genuine measurable local-product protocols.
The input information bound concerns every original product POVM.  The proof
instantiates it at each chosen setting, uses actual stopped Born execution,
then takes the promised-state supremum and full protocol-class infimum.
Costs and division remain in ENNReal, including infinite expected costs.
The analytic target event supplying the uniform bound is a separate theorem. -/

set_option autoImplicit false
open MeasureTheory InformationTheory LocalCertification.Quantum
open scoped ENNReal
noncomputable section

namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u
variable {d n : ℕ} [NeZero d]

theorem expectedBudget_lower_high_low
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1/2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hρ : a ≤ pureTargetFidelity ψ ρ) (hσ : pureTargetFidelity ψ σ ≤ b)
    (Γ : ℝ) (hΓ : 0 < Γ)
    (hstep : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      klDiv ((MeasurablePOVM.product M).born ρ) ((MeasurablePOVM.product M).born σ) ≤ ENNReal.ofReal Γ) :
    ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) / ENNReal.ofReal Γ ≤
      expectedBudget.{u} ψ a b δ := by
  apply expectedBudget_lower
  intro Z S Ω mZ mS mΩ P hv
  have hi := P.toBorn.information_of_valid_high_low ψ a b δ hδ hhalf hv ρ σ hρ hσ Γ hΓ.le
    (fun s => hstep Ω (fun i => (P.localFamilies i).measurement s))
  have hc := (ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr hΓ)) ENNReal.ofReal_ne_top).mpr hi
  exact hc.trans (expectedCopies_le_protocolCost P ψ a b ρ (Or.inl hρ))

theorem expectedBudget_lower_low_high
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1/2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hρ : pureTargetFidelity ψ ρ ≤ b) (hσ : a ≤ pureTargetFidelity ψ σ)
    (Γ : ℝ) (hΓ : 0 < Γ)
    (hstep : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      klDiv ((MeasurablePOVM.product M).born ρ) ((MeasurablePOVM.product M).born σ) ≤ ENNReal.ofReal Γ) :
    ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) / ENNReal.ofReal Γ ≤
      expectedBudget.{u} ψ a b δ := by
  apply expectedBudget_lower
  intro Z S Ω mZ mS mΩ P hv
  have hi := P.toBorn.information_of_valid_low_high ψ a b δ hδ hhalf hv ρ σ hρ hσ Γ hΓ.le
    (fun s => hstep Ω (fun i => (P.localFamilies i).measurement s))
  have hc := (ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr hΓ)) ENNReal.ofReal_ne_top).mpr hi
  exact hc.trans (expectedCopies_le_protocolCost P ψ a b ρ (Or.inr hρ))

/-- The high/low ordering charges the actual high state's expected cost,
then optimizes over every valid product protocol in the declared universe. -/
theorem budget_bounds_high_low
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1/2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hρ : a ≤ pureTargetFidelity ψ ρ) (hσ : pureTargetFidelity ψ σ ≤ b)
    (Γ : ℝ) (hΓ : 0 < Γ)
    (hstep : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      klDiv ((MeasurablePOVM.product M).born ρ) ((MeasurablePOVM.product M).born σ) ≤ ENNReal.ofReal Γ) :
    ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) / ENNReal.ofReal Γ ≤
      expectedBudget.{u} ψ a b δ ∧
    expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} ψ a b δ) :=
  ⟨expectedBudget_lower_high_low ψ a b δ hδ hhalf ρ σ hρ hσ Γ hΓ hstep,
    expectedBudget_le_maximumBudget ψ a b δ⟩

/-- The opposite ordering charges the actual low state and retains the same
exact testing factor and extended-valued budget comparison. -/
theorem budget_bounds_low_high
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1/2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hρ : pureTargetFidelity ψ ρ ≤ b) (hσ : a ≤ pureTargetFidelity ψ σ)
    (Γ : ℝ) (hΓ : 0 < Γ)
    (hstep : ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
      (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
      klDiv ((MeasurablePOVM.product M).born ρ) ((MeasurablePOVM.product M).born σ) ≤ ENNReal.ofReal Γ) :
    ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) / ENNReal.ofReal Γ ≤
      expectedBudget.{u} ψ a b δ ∧
    expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} ψ a b δ) :=
  ⟨expectedBudget_lower_low_high ψ a b δ hδ hhalf ρ σ hρ hσ Γ hΓ hstep,
    expectedBudget_le_maximumBudget ψ a b δ⟩

end LocalCertification.Protocol.MeasurableExecution.ProductBudget
