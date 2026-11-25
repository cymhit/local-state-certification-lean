import LocalCertification.Protocol.CanonicalProtocol

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {d n : ℕ} [NeZero d]

/-- Only the two promised classes enter the worst-case expected cost. -/
def promisedStates (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) :
    Set (QIT.State (CertificationGaussian.QuditIndex d n)) := {ρ | a ≤ pureTargetFidelity ψ ρ ∨ pureTargetFidelity ψ ρ ≤ b}

/-- First fix the protocol, then take the extended supremum over all promised inputs. Empty promise sets give zero. -/
def protocolCost {Z : Type u} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ ρ : promisedStates ψ a b, expectedCopies P ρ.val

/-- The infimum is over the fixed small canonical type and valid protocols only; empty feasibility gives infinity. -/
def expectedBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : ℝ≥0∞ :=
  ⨅ Q : CanonicalProtocol d n, ⨅ (_ : Valid Q.toRaw ψ a b δ), protocolCost Q.toRaw ψ a b

/-- Feasible copy caps quantify over every path, not merely almost-sure stopping. -/
def capFeasible (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) (N : ℕ) : Prop :=
  ∃ Q : CanonicalProtocol d n, Valid Q.toRaw ψ a b δ ∧ Capped Q.toRaw N

/-- The exact least feasible natural cap, or infinity when no cap is feasible. -/
def maximumBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : WithTop ℕ := by
  classical
  exact if h : ∃ N, capFeasible ψ a b δ N then (Nat.find h : WithTop ℕ) else ⊤

theorem expectedCopies_le_protocolCost {Z : Type u} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (hρ : ρ ∈ promisedStates ψ a b) :
    expectedCopies P ρ ≤ protocolCost P ψ a b := le_iSup (fun ρ : promisedStates ψ a b => expectedCopies P ρ.val) ⟨ρ,hρ⟩

theorem protocolCost_le_of_capped {Z : Type u} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) (N : ℕ) (hN : Capped P N) :
    protocolCost P ψ a b ≤ (N : ℝ≥0∞) :=
  iSup_le (fun ρ => expectedCopies_le_of_capped P N hN ρ.val)

theorem normalizeProtocol_cost {Z : Type u} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ) :
    protocolCost (normalizeProtocol P).toRaw ψ a b = protocolCost P ψ a b := by
  unfold protocolCost
  simp only [normalizeProtocol_expectedCopies]

/-- Canonical budgeting covers every original seed universe, by the proved full-image normalization. -/
theorem expectedBudget_le_raw_cost {Z : Type u} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) (hv : Valid P ψ a b δ) :
    expectedBudget ψ a b δ ≤ protocolCost P ψ a b := by
  rw [← normalizeProtocol_cost P ψ a b]
  exact iInf_le_of_le (normalizeProtocol P)
    (iInf_le_of_le ((normalizeProtocol_valid_iff P ψ a b δ).mpr hv) le_rfl)

theorem expectedBudget_lower (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (B : ℝ≥0∞) (h : ∀ Q : CanonicalProtocol d n, Valid Q.toRaw ψ a b δ → B ≤ protocolCost Q.toRaw ψ a b) :
    B ≤ expectedBudget ψ a b δ := le_iInf (fun Q => le_iInf (fun hv => h Q hv))

theorem maximumBudget_eq_top_iff (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    maximumBudget ψ a b δ = ⊤ ↔ ¬∃ N, capFeasible ψ a b δ N := by
  classical
  by_cases h : ∃ N, capFeasible ψ a b δ N
  · simp [maximumBudget, h]
  · simp [maximumBudget, h]

/-- Every finite maximum budget has an actual valid canonical protocol attaining that natural cap. -/
theorem maximumBudget_attained (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (h : maximumBudget ψ a b δ ≠ ⊤) :
    ∃ N : ℕ, maximumBudget ψ a b δ = (N : WithTop ℕ) ∧ capFeasible ψ a b δ N := by
  classical
  have hex : ∃ N, capFeasible ψ a b δ N := not_not.mp ((maximumBudget_eq_top_iff ψ a b δ).not.mp h)
  exact ⟨Nat.find hex, by simp [maximumBudget,hex], Nat.find_spec hex⟩

theorem maximumBudget_le_of_feasible (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (N : ℕ) (hN : capFeasible ψ a b δ N) : maximumBudget ψ a b δ ≤ (N : WithTop ℕ) := by
  classical
  have hex : ∃ M, capFeasible ψ a b δ M := ⟨N,hN⟩
  simp only [maximumBudget, dite_eq_left hex, Nat.cast_le]
  exact Nat.find_min' hex hN

/-- The expected budget never exceeds the embedded exact maximum budget, including infinity. -/
theorem expectedBudget_le_maximumBudget (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) :
    expectedBudget ψ a b δ ≤ ENat.toENNReal (maximumBudget ψ a b δ) := by
  by_cases ht : maximumBudget ψ a b δ = ⊤
  · rw [ht]
    exact le_top
  · obtain ⟨N,hN,Q,hvalid,hcap⟩ := maximumBudget_attained ψ a b δ ht
    rw [hN]
    exact (expectedBudget_le_raw_cost Q.toRaw ψ a b δ hvalid).trans
      (protocolCost_le_of_capped Q.toRaw ψ a b N hcap)

/-- Empty promised sets have zero worst-case extended cost. -/
theorem protocolCost_eq_zero_of_no_promises {Z : Type u} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b : ℝ)
    (h : ∀ ρ, ρ ∉ promisedStates ψ a b) : protocolCost P ψ a b = 0 := by
  apply le_antisymm
  · exact iSup_le (fun ρ => False.elim (h ρ.val ρ.property))
  · exact bot_le

/-- Empty validity feasibility has extended infimum infinity; no attainment is asserted. -/
theorem expectedBudget_eq_top_of_no_valid (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (h : ∀ Q : CanonicalProtocol d n, ¬Valid Q.toRaw ψ a b δ) : expectedBudget ψ a b δ = ∞ := by
  apply top_unique
  exact le_iInf (fun Q => le_iInf (fun hv => False.elim (h Q hv)))

/-- An actual raw protocol with a cap supplies a feasible canonical cap, including all null paths. -/
theorem capFeasible_of_raw {Z : Type u} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : Valid P ψ a b δ) (N : ℕ) (hN : Capped P N) : capFeasible ψ a b δ N :=
  ⟨normalizeProtocol P, (normalizeProtocol_valid_iff P ψ a b δ).mpr hv,
    (normalizeProtocol_capped_iff P N).mpr hN⟩

theorem maximumBudget_le_raw_cap {Z : Type u} [MeasurableSpace Z] (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hv : Valid P ψ a b δ) (N : ℕ) (hN : Capped P N) : maximumBudget ψ a b δ ≤ (N : WithTop ℕ) :=
  maximumBudget_le_of_feasible ψ a b δ N (capFeasible_of_raw P ψ a b δ hv N hN)

end LocalCertification.Protocol
