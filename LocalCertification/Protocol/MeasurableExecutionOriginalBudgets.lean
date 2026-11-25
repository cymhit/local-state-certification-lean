import LocalCertification.Protocol.MeasurableExecutionUniverse
import LocalCertification.Protocol.MeasurableExecutionBudgets

/-! Original independent-universe protocols enter the general optimization
with their literal input laws, extended costs and all-legal-path caps. -/
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u v w
variable {d n : ℕ} [NeZero d] {Z : Type u} {S : Type v} {Ω : Fin n → Type w}
  [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]

namespace OriginalProductProtocol

def protocolCost (P : OriginalProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ ρ : ProductBudget.promisedStates ψ a b, P.expectedCopies ρ.val

theorem protocolCost_eq_aligned (P : OriginalProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) :
    P.protocolCost ψ a b = ProductBudget.protocolCost P.aligned ψ a b := by
  apply congrArg iSup
  funext ρ
  exact P.expectedCopies_eq_aligned ρ.val

theorem expectedBudget_le_protocolCost (P : OriginalProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) : ProductBudget.expectedBudget.{max u v w} ψ a b δ ≤ P.protocolCost ψ a b :=
  (ProductBudget.expectedBudget_le_protocolCost P.aligned ψ a b δ
    ((P.valid_iff_aligned ψ a b δ).mp hv)).trans_eq (P.protocolCost_eq_aligned ψ a b).symm

theorem capFeasible_of_capped (P : OriginalProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) (N : ℕ) (hc : P.Capped N) :
    ProductBudget.capFeasible.{max u v w} ψ a b δ N :=
  ProductBudget.capFeasible_of_protocol P.aligned ψ a b δ
    ((P.valid_iff_aligned ψ a b δ).mp hv) N ((P.capped_iff N).mpr hc)

theorem maximumBudget_le_cap (P : OriginalProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) (N : ℕ) (hc : P.Capped N) :
    ProductBudget.maximumBudget.{max u v w} ψ a b δ ≤ (N : ℕ∞) :=
  ProductBudget.maximumBudget_le_of_feasible ψ a b δ N (P.capFeasible_of_capped ψ a b δ hv N hc)

end OriginalProductProtocol

theorem original_protocol_budget_embedding (P : OriginalProductProtocol d n Z S Ω)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) :
    ProductBudget.expectedBudget.{max u v w} ψ a b δ ≤
      ⨆ ρ : ProductBudget.promisedStates ψ a b,
        ∫⁻ p, ENat.toENNReal (P.time p) ∂P.law ρ.val ∧
    ∀ N : ℕ, P.Capped N →
      ProductBudget.capFeasible.{max u v w} ψ a b δ N ∧
      ProductBudget.maximumBudget.{max u v w} ψ a b δ ≤ (N : ℕ∞) :=
  ⟨P.expectedBudget_le_protocolCost ψ a b δ hv, fun N hc =>
    ⟨P.capFeasible_of_capped ψ a b δ hv N hc, P.maximumBudget_le_cap ψ a b δ hv N hc⟩⟩

end LocalCertification.Protocol.MeasurableExecution
