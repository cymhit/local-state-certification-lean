import LocalCertification.Protocol.MeasurableHistoryExtension
import LocalCertification.Protocol.MeasurableHistoryEmpty
import LocalCertification.Protocol.MeasurableHistoryOfSetting
import LocalCertification.Protocol.MeasurableExecutionBudgets

/-! Exact equivalence of the paper's history-dependent global-product model
and the setting-family model used by the hierarchy. Both optimizations retain
infinite costs, arbitrary measurable spaces, and caps on every legal path. -/
set_option autoImplicit false
open MeasureTheory LocalCertification.Quantum
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u
variable {d n : ℕ} [NeZero d]

namespace PaperHistoryProduct
variable {Z L : Type u} {Ω : Fin n → Type u}
  [MeasurableSpace Z] [MeasurableSpace L] [∀ i, MeasurableSpace (Ω i)]
variable (P : PaperHistoryProduct d n Z L Ω)

/-- Every paper-model protocol has an actual setting-family implementation.
The result includes protocols which never measure and empty outcome spaces. -/
theorem exists_compile : ∃ (S : Type u) (mS : MeasurableSpace S),
    let := mS
    ∃ Q : ProductProtocol d n Z S Ω, P.Preserves Q := by
  classical
  by_cases h : ∃ t, Nonempty {h // h ∈ continuingContexts P.raw.toRawRules t}
  · obtain ⟨Q, hQ⟩ := P.exists_compile_of_live h
    exact ⟨HistorySetting Z L ((i : Fin n) → Ω i), inferInstance, Q, hQ⟩
  · obtain ⟨Q, hQ⟩ := P.exists_compile_of_no_live h
    exact ⟨PEmpty.{u+1}, inferInstance, Q, hQ⟩

def protocolCost (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ ρ : ProductBudget.promisedStates ψ a b, P.expectedCopies ρ.val

theorem Preserves.protocolCost_eq {P : PaperHistoryProduct d n Z L Ω}
    {S : Type u} [MeasurableSpace S] {Q : ProductProtocol d n Z S Ω} (h : P.Preserves Q)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) :
    ProductBudget.protocolCost Q ψ a b = P.protocolCost ψ a b := by
  apply congrArg iSup
  funext ρ
  exact h.expectedCopies_eq ρ.val

theorem expectedBudget_le_protocolCost
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) : ProductBudget.expectedBudget.{u} ψ a b δ ≤ P.protocolCost ψ a b := by
  obtain ⟨S, mS, Q, hQ⟩ := P.exists_compile
  let := mS
  exact (ProductBudget.expectedBudget_le_protocolCost Q ψ a b δ
    ((hQ.valid_iff ψ a b δ).mpr hv)).trans_eq (hQ.protocolCost_eq ψ a b)

theorem capFeasible_of_capped
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) (N : ℕ) (hc : P.Capped N) :
    ProductBudget.capFeasible.{u} ψ a b δ N := by
  obtain ⟨S, mS, Q, hQ⟩ := P.exists_compile
  let := mS
  exact ProductBudget.capFeasible_of_protocol Q ψ a b δ
    ((hQ.valid_iff ψ a b δ).mpr hv) N ((hQ.capped_iff N).mpr hc)

theorem maximumBudget_le_cap
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : P.Valid ψ a b δ) (N : ℕ) (hc : P.Capped N) :
    ProductBudget.maximumBudget.{u} ψ a b δ ≤ (N : ℕ∞) :=
  ProductBudget.maximumBudget_le_of_feasible ψ a b δ N (P.capFeasible_of_capped ψ a b δ hv N hc)

end PaperHistoryProduct

namespace PaperHistoryBudget

/-- The paper representation's own optimization, defined before using any
equivalence with the setting-family infimum. -/
def expectedBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : ℝ≥0∞ :=
  ⨅ (Z : Type u) (L : Type u) (Ω : Fin n → Type u) (mZ : MeasurableSpace Z) (mL : MeasurableSpace L)
    (mΩ : ∀ i, MeasurableSpace (Ω i)),
    let := mZ
    let := mL
    let := mΩ
    ⨅ (P : PaperHistoryProduct d n Z L Ω) (_ : P.Valid ψ a b δ), P.protocolCost ψ a b

def capFeasible (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) (N : ℕ) : Prop :=
  ∃ (Z L : Type u) (Ω : Fin n → Type u) (mZ : MeasurableSpace Z) (mL : MeasurableSpace L)
    (mΩ : ∀ i, MeasurableSpace (Ω i)),
    let := mZ
    let := mL
    let := mΩ
    ∃ P : PaperHistoryProduct d n Z L Ω, P.Valid ψ a b δ ∧ P.Capped N

def maximumBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : ℕ∞ := by
  classical
  exact if h : ∃ N, capFeasible.{u} ψ a b δ N then (Nat.find h : ℕ∞) else ⊤

theorem expectedBudget_le_protocolCost {Z L : Type u} {Ω : Fin n → Type u}
    [mZ : MeasurableSpace Z] [mL : MeasurableSpace L] [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (P : PaperHistoryProduct d n Z L Ω) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) (hv : P.Valid ψ a b δ) : expectedBudget.{u} ψ a b δ ≤ P.protocolCost ψ a b := by
  unfold expectedBudget
  exact iInf_le_of_le Z (iInf_le_of_le L (iInf_le_of_le Ω (iInf_le_of_le mZ
    (iInf_le_of_le mL (iInf_le_of_le mΩ (iInf_le_of_le P (iInf_le_of_le hv le_rfl)))))))

/-- The extended infima agree exactly, including empty-validity and infinite
expected-cost cases. This theorem supplies the model boundary for all existing
expected-budget hierarchy statements without changing their types. -/
theorem expectedBudget_eq (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    expectedBudget.{u} ψ a b δ = ProductBudget.expectedBudget.{u} ψ a b δ := by
  apply le_antisymm
  · unfold ProductBudget.expectedBudget
    refine le_iInf (fun Z => le_iInf (fun S => le_iInf (fun Ω => le_iInf (fun mZ =>
      le_iInf (fun mS => le_iInf (fun mΩ => ?_))))))
    let := mZ
    let := mS
    let := mΩ
    refine le_iInf (fun Q => le_iInf (fun hv => ?_))
    have hQ := PaperHistoryProduct.ofSetting_preserves Q
    exact (expectedBudget_le_protocolCost (PaperHistoryProduct.ofSetting Q) ψ a b δ
      ((hQ.valid_iff ψ a b δ).mp hv)).trans_eq (hQ.protocolCost_eq ψ a b).symm
  · unfold expectedBudget
    refine le_iInf (fun Z => le_iInf (fun L => le_iInf (fun Ω => le_iInf (fun mZ =>
      le_iInf (fun mL => le_iInf (fun mΩ => ?_))))))
    let := mZ
    let := mL
    let := mΩ
    exact le_iInf (fun P => le_iInf (fun hv => P.expectedBudget_le_protocolCost ψ a b δ hv))

theorem capFeasible_iff (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) (N : ℕ) : capFeasible.{u} ψ a b δ N ↔ ProductBudget.capFeasible.{u} ψ a b δ N := by
  constructor
  · rintro ⟨Z, L, Ω, mZ, mL, mΩ, P, hv, hc⟩
    let := mZ
    let := mL
    let := mΩ
    exact P.capFeasible_of_capped ψ a b δ hv N hc
  · rintro ⟨Z, S, Ω, mZ, mS, mΩ, Q, hv, hc⟩
    let := mZ
    let := mS
    let := mΩ
    have hQ := PaperHistoryProduct.ofSetting_preserves Q
    exact ⟨Z, S, Ω, mZ, mS, mΩ, PaperHistoryProduct.ofSetting Q,
      (hQ.valid_iff ψ a b δ).mp hv, (hQ.capped_iff N).mp hc⟩

/-- Equality of least feasible all-legal-path caps, including infinity. -/
theorem maximumBudget_eq (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    maximumBudget.{u} ψ a b δ = ProductBudget.maximumBudget.{u} ψ a b δ := by
  classical
  have he : capFeasible.{u} ψ a b δ = ProductBudget.capFeasible.{u} ψ a b δ :=
    funext (fun N => propext (capFeasible_iff ψ a b δ N))
  unfold maximumBudget ProductBudget.maximumBudget
  rw [he]

theorem budget_equivalence (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    expectedBudget.{u} ψ a b δ = ProductBudget.expectedBudget.{u} ψ a b δ ∧
    maximumBudget.{u} ψ a b δ = ProductBudget.maximumBudget.{u} ψ a b δ ∧
    ∀ N, capFeasible.{u} ψ a b δ N ↔ ProductBudget.capFeasible.{u} ψ a b δ N :=
  ⟨expectedBudget_eq ψ a b δ, maximumBudget_eq ψ a b δ, capFeasible_iff ψ a b δ⟩

end PaperHistoryBudget
end LocalCertification.Protocol.MeasurableExecution
