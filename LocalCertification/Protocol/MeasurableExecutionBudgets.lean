import LocalCertification.Protocol.MeasurableExecutionProduct
import LocalCertification.Protocol.Budgets

/-! Optimization over the full measurable local-product protocol class in a
declared universe. No canonical finite tree represents or restricts this class.
The expected cost is extended and only promised inputs enter its supremum. -/
set_option autoImplicit false
open MeasureTheory LocalCertification.Quantum
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u
variable {d n : ℕ} [NeZero d]

def promisedStates (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) :=
  {ρ : QIT.State (CertificationGaussian.QuditIndex d n) | a ≤ pureTargetFidelity ψ ρ ∨ pureTargetFidelity ψ ρ ≤ b}

def protocolCost {Z S : Type u} {Ω : Fin n → Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
    (P : ProductProtocol d n Z S Ω) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b : ℝ) : ℝ≥0∞ := ⨆ ρ : promisedStates ψ a b, P.toBorn.expectedCopies ρ.val

/-- The quantifiers retain every seed, setting, local outcome type and their
original measurable spaces in universe u. Empty validity gives infinity. -/
def expectedBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : ℝ≥0∞ :=
  ⨅ (Z : Type u) (S : Type u) (Ω : Fin n → Type u) (mZ : MeasurableSpace Z) (mS : MeasurableSpace S)
    (mΩ : ∀ i, MeasurableSpace (Ω i)),
    letI := mZ
    letI := mS
    letI := mΩ
    ⨅ (P : ProductProtocol d n Z S Ω) (_ : P.toBorn.Valid ψ a b δ), protocolCost P ψ a b

/-- Feasibility retains an actual protocol and an every-legal-path cap,
including null seeds and impossible-outcome branches. -/
def capFeasible (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) (N : ℕ) : Prop :=
  ∃ (Z S : Type u) (Ω : Fin n → Type u) (mZ : MeasurableSpace Z) (mS : MeasurableSpace S)
    (mΩ : ∀ i, MeasurableSpace (Ω i)),
    letI := mZ
    letI := mS
    letI := mΩ
    ∃ P : ProductProtocol d n Z S Ω, P.toBorn.Valid ψ a b δ ∧ P.toBorn.Capped N

def maximumBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : ℕ∞ := by
  classical
  exact if h : ∃ N, capFeasible.{u} ψ a b δ N then (Nat.find h : ℕ∞) else ⊤

theorem expectedCopies_le_protocolCost {Z S : Type u} {Ω : Fin n → Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
    (P : ProductProtocol d n Z S Ω) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b : ℝ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (hρ : ρ ∈ promisedStates ψ a b) :
    P.toBorn.expectedCopies ρ ≤ protocolCost P ψ a b :=
  le_iSup (fun ρ : promisedStates ψ a b => P.toBorn.expectedCopies ρ.val) ⟨ρ, hρ⟩

theorem protocolCost_le_of_capped {Z S : Type u} {Ω : Fin n → Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
    (P : ProductProtocol d n Z S Ω) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b : ℝ) (N : ℕ) (h : P.toBorn.Capped N) : protocolCost P ψ a b ≤ (N : ℝ≥0∞) :=
  iSup_le (fun ρ => P.toBorn.capped_expectedCopies N h ρ.val)

theorem expectedBudget_le_protocolCost {Z S : Type u} {Ω : Fin n → Type u}
    [mZ : MeasurableSpace Z] [mS : MeasurableSpace S] [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (P : ProductProtocol d n Z S Ω) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) (hv : P.toBorn.Valid ψ a b δ) :
    expectedBudget.{u} ψ a b δ ≤ protocolCost P ψ a b := by
  unfold expectedBudget
  exact iInf_le_of_le Z (iInf_le_of_le S (iInf_le_of_le Ω (iInf_le_of_le mZ
    (iInf_le_of_le mS (iInf_le_of_le mΩ (iInf_le_of_le P (iInf_le_of_le hv le_rfl)))))))

/-- A uniform lower bound on genuine valid protocols passes to the complete
optimization class; no finite expectation or cap is assumed. -/
theorem expectedBudget_lower (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) (B : ℝ≥0∞)
    (h : ∀ (Z S : Type u) (Ω : Fin n → Type u) [MeasurableSpace Z] [MeasurableSpace S]
      [∀ i, MeasurableSpace (Ω i)] (P : ProductProtocol d n Z S Ω),
      P.toBorn.Valid ψ a b δ → B ≤ protocolCost P ψ a b) :
    B ≤ expectedBudget.{u} ψ a b δ := by
  unfold expectedBudget
  refine le_iInf (fun Z => le_iInf (fun S => le_iInf (fun Ω => le_iInf (fun mZ =>
    le_iInf (fun mS => le_iInf (fun mΩ => ?_))))))
  let := mZ
  let := mS
  let := mΩ
  exact le_iInf (fun P => le_iInf (fun hv => h Z S Ω P hv))

theorem capFeasible_of_protocol {Z S : Type u} {Ω : Fin n → Type u}
    [mZ : MeasurableSpace Z] [mS : MeasurableSpace S] [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (P : ProductProtocol d n Z S Ω) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) (hv : P.toBorn.Valid ψ a b δ) (N : ℕ) (hN : P.toBorn.Capped N) :
    capFeasible.{u} ψ a b δ N := ⟨Z, S, Ω, mZ, mS, mΩ, P, hv, hN⟩

theorem maximumBudget_eq_top_iff (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    maximumBudget.{u} ψ a b δ = ⊤ ↔ ¬∃ N, capFeasible.{u} ψ a b δ N := by
  classical
  by_cases h : ∃ N, capFeasible.{u} ψ a b δ N <;> simp [maximumBudget, h]

theorem maximumBudget_attained (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (h : maximumBudget.{u} ψ a b δ ≠ ⊤) :
    ∃ N : ℕ, maximumBudget.{u} ψ a b δ = (N : ℕ∞) ∧ capFeasible.{u} ψ a b δ N := by
  classical
  have hex : ∃ N, capFeasible.{u} ψ a b δ N :=
    not_not.mp ((maximumBudget_eq_top_iff ψ a b δ).not.mp h)
  exact ⟨Nat.find hex, by simp [maximumBudget, hex], Nat.find_spec hex⟩

theorem maximumBudget_le_of_feasible (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (N : ℕ) (hN : capFeasible.{u} ψ a b δ N) : maximumBudget.{u} ψ a b δ ≤ (N : ℕ∞) := by
  classical
  have hex : ∃ M, capFeasible.{u} ψ a b δ M := ⟨N, hN⟩
  simp only [maximumBudget, dite_eq_left hex, Nat.cast_le]
  exact Nat.find_min' hex hN

theorem expectedBudget_le_maximumBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) : expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} ψ a b δ) := by
  by_cases ht : maximumBudget.{u} ψ a b δ = ⊤
  · rw [ht, ENat.toENNReal_top]
    exact le_top
  · obtain ⟨N, hN, Z, S, Ω, mZ, mS, mΩ, P, hv, hc⟩ := maximumBudget_attained ψ a b δ ht
    let := mZ
    let := mS
    let := mΩ
    rw [hN, ENat.toENNReal_coe]
    exact (expectedBudget_le_protocolCost P ψ a b δ hv).trans (protocolCost_le_of_capped P ψ a b N hc)

theorem maximumBudget_le_protocol_cap {Z S : Type u} {Ω : Fin n → Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
    (P : ProductProtocol d n Z S Ω) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) (hv : P.toBorn.Valid ψ a b δ) (N : ℕ) (hc : P.toBorn.Capped N) :
    maximumBudget.{u} ψ a b δ ≤ (N : ℕ∞) :=
  maximumBudget_le_of_feasible ψ a b δ N (capFeasible_of_protocol P ψ a b δ hv N hc)

/-- The finite-outcome basis protocol is only a proved subclass for upper
bounds. It does not define or normalize the general optimization domain. -/
theorem basis_capFeasible {Z : Type} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : Protocol.Valid P ψ a b δ) (N : ℕ) (hc : Protocol.Capped P N) :
    capFeasible.{0} ψ a b δ N := by
  refine capFeasible_of_protocol (basisProductProtocol P) ψ a b δ ?_ N ?_
  · rw [basisProductProtocol_toBorn]
    exact (basisProtocol_valid_iff P ψ a b δ).mpr hv
  · rw [basisProductProtocol_toBorn]
    exact (basisProtocol_capped_iff P N).mpr hc

theorem expectedBudget_le_basisBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) : expectedBudget.{0} ψ a b δ ≤ Protocol.expectedBudget ψ a b δ := by
  apply le_iInf
  intro Q
  apply le_iInf
  intro hv
  have h := expectedBudget_le_protocolCost (basisProductProtocol Q.toRaw) ψ a b δ
    (by rw [basisProductProtocol_toBorn]; exact (basisProtocol_valid_iff Q.toRaw ψ a b δ).mpr hv)
  simpa only [protocolCost, Protocol.protocolCost, basisProductProtocol_toBorn,
    basisProtocol_expectedCopies, promisedStates, Protocol.promisedStates] using h

theorem maximumBudget_le_basisBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) : maximumBudget.{0} ψ a b δ ≤ Protocol.maximumBudget ψ a b δ := by
  by_cases ht : Protocol.maximumBudget ψ a b δ = ⊤
  · rw [ht]
    exact le_top
  · obtain ⟨N, hN, Q, hv, hc⟩ := Protocol.maximumBudget_attained ψ a b δ ht
    rw [hN]
    exact maximumBudget_le_of_feasible ψ a b δ N (basis_capFeasible Q.toRaw ψ a b δ hv N hc)

end LocalCertification.Protocol.MeasurableExecution.ProductBudget

namespace LocalCertification.Protocol.MeasurableExecution
universe u
variable {d n : ℕ} [NeZero d]

theorem product_budget_contract (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    ProductBudget.expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (ProductBudget.maximumBudget.{u} ψ a b δ) ∧
    (ProductBudget.maximumBudget.{u} ψ a b δ = ⊤ ↔ ¬∃ N, ProductBudget.capFeasible.{u} ψ a b δ N) ∧
    (ProductBudget.maximumBudget.{u} ψ a b δ ≠ ⊤ → ∃ N : ℕ,
      ProductBudget.maximumBudget.{u} ψ a b δ = (N : ℕ∞) ∧ ProductBudget.capFeasible.{u} ψ a b δ N) ∧
    (∀ N, ProductBudget.capFeasible.{u} ψ a b δ N → ProductBudget.maximumBudget.{u} ψ a b δ ≤ (N : ℕ∞)) :=
  ⟨ProductBudget.expectedBudget_le_maximumBudget ψ a b δ,
    ProductBudget.maximumBudget_eq_top_iff ψ a b δ, ProductBudget.maximumBudget_attained ψ a b δ,
    ProductBudget.maximumBudget_le_of_feasible ψ a b δ⟩

end LocalCertification.Protocol.MeasurableExecution
