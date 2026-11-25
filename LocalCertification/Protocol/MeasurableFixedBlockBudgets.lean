import LocalCertification.Protocol.MeasurableFixedBlockProtocol
import LocalCertification.Protocol.MeasurableExecutionBudgets

/-! The fixed-block budgets optimize expected and maximum physical copy costs
over measurable protocols. The prescribed partition is fixed throughout the protocol. -/
set_option autoImplicit false
open MeasureTheory LocalCertification.Quantum CertificationGaussian
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.FixedBlock
universe u
variable {k m : ℕ}

def protocolCost {Z S : Type u} {Ω : Fin m → Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
    (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ ρ : {ρ : QIT.State (QuditIndex 2 (k*m)) // a ≤ pureTargetFidelity ψ ρ ∨ pureTargetFidelity ψ ρ ≤ b},
    (physical P Q).expectedCopies ρ.val

theorem protocolCost_eq {Z S : Type u} {Ω : Fin m → Type u}
    [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]
    (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b : ℝ) :
    protocolCost P Q ψ a b = ProductBudget.protocolCost Q (ψ.reindex (fixedBlockIndexEquiv P)) a b := by
  unfold protocolCost ProductBudget.protocolCost
  apply le_antisymm
  · apply iSup_le
    intro ρ
    have hf : ρ.val.reindex (fixedBlockIndexEquiv P) ∈
        ProductBudget.promisedStates (ψ.reindex (fixedBlockIndexEquiv P)) a b := by
      change a ≤ pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P)) (ρ.val.reindex (fixedBlockIndexEquiv P)) ∨
        pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P)) (ρ.val.reindex (fixedBlockIndexEquiv P)) ≤ b
      rw [pureTargetFidelity_reindex]
      exact ρ.property
    exact le_iSup_of_le ⟨ρ.val.reindex (fixedBlockIndexEquiv P), hf⟩
      (physical_expectedCopies P Q ρ.val).le
  · apply iSup_le
    intro σ
    obtain ⟨ρ, hρ⟩ := (stateReindexEquiv (fixedBlockIndexEquiv P)).surjective σ.val
    have hf : a ≤ pureTargetFidelity ψ ρ ∨ pureTargetFidelity ψ ρ ≤ b := by
      have h := σ.property
      change a ≤ pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P)) σ.val ∨
        pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P)) σ.val ≤ b at h
      rw [← hρ] at h
      change a ≤ pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P)) (ρ.reindex (fixedBlockIndexEquiv P)) ∨
        pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P)) (ρ.reindex (fixedBlockIndexEquiv P)) ≤ b at h
      rwa [pureTargetFidelity_reindex] at h
    apply le_iSup_of_le ⟨ρ, hf⟩
    rw [physical_expectedCopies]
    change Q.toBorn.expectedCopies σ.val ≤ Q.toBorn.expectedCopies ((stateReindexEquiv (fixedBlockIndexEquiv P)) ρ)
    rw [hρ]

def expectedBudget (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) : ℝ≥0∞ :=
  ⨅ (Z : Type u) (S : Type u) (Ω : Fin m → Type u) (mZ : MeasurableSpace Z) (mS : MeasurableSpace S)
    (mΩ : ∀ i, MeasurableSpace (Ω i)),
    letI := mZ
    letI := mS
    letI := mΩ
    ⨅ (Q : ProductProtocol (2^k) m Z S Ω) (_ : (physical P Q).Valid ψ a b δ), protocolCost P Q ψ a b

def capFeasible (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) (N : ℕ) : Prop :=
  ∃ (Z S : Type u) (Ω : Fin m → Type u) (mZ : MeasurableSpace Z) (mS : MeasurableSpace S)
    (mΩ : ∀ i, MeasurableSpace (Ω i)),
    letI := mZ
    letI := mS
    letI := mΩ
    ∃ Q : ProductProtocol (2^k) m Z S Ω, (physical P Q).Valid ψ a b δ ∧ (physical P Q).Capped N

def maximumBudget (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) : ℕ∞ := by
  classical
  exact if h : ∃ N, capFeasible.{u} P ψ a b δ N then (Nat.find h : ℕ∞) else ⊤

theorem expectedBudget_le_protocolCost {Z S : Type u} {Ω : Fin m → Type u}
    [mZ : MeasurableSpace Z] [mS : MeasurableSpace S] [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) (hv : (physical P Q).Valid ψ a b δ) :
    expectedBudget.{u} P ψ a b δ ≤ protocolCost P Q ψ a b := by
  unfold expectedBudget
  exact iInf_le_of_le Z (iInf_le_of_le S (iInf_le_of_le Ω (iInf_le_of_le mZ
    (iInf_le_of_le mS (iInf_le_of_le mΩ (iInf_le_of_le Q (iInf_le_of_le hv le_rfl)))))))

theorem expectedBudget_eq (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    expectedBudget.{u} P ψ a b δ = ProductBudget.expectedBudget.{u} (ψ.reindex (fixedBlockIndexEquiv P)) a b δ := by
  apply le_antisymm
  · unfold ProductBudget.expectedBudget
    refine le_iInf (fun Z => le_iInf (fun S => le_iInf (fun Ω => le_iInf (fun mZ =>
      le_iInf (fun mS => le_iInf (fun mΩ => ?_))))))
    let := mZ
    let := mS
    let := mΩ
    refine le_iInf (fun Q => le_iInf (fun hv => ?_))
    exact (expectedBudget_le_protocolCost P Q ψ a b δ ((physical_valid_iff P Q ψ a b δ).mpr hv)).trans_eq
      (protocolCost_eq P Q ψ a b)
  · unfold expectedBudget
    refine le_iInf (fun Z => le_iInf (fun S => le_iInf (fun Ω => le_iInf (fun mZ =>
      le_iInf (fun mS => le_iInf (fun mΩ => ?_))))))
    let := mZ
    let := mS
    let := mΩ
    refine le_iInf (fun Q => le_iInf (fun hv => ?_))
    exact (ProductBudget.expectedBudget_le_protocolCost Q (ψ.reindex (fixedBlockIndexEquiv P)) a b δ
      ((physical_valid_iff P Q ψ a b δ).mp hv)).trans_eq (protocolCost_eq P Q ψ a b).symm

theorem capFeasible_iff (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) (N : ℕ) :
    capFeasible.{u} P ψ a b δ N ↔ ProductBudget.capFeasible.{u} (ψ.reindex (fixedBlockIndexEquiv P)) a b δ N := by
  constructor
  · rintro ⟨Z, S, Ω, mZ, mS, mΩ, Q, hv, hc⟩
    let := mZ
    let := mS
    let := mΩ
    exact ⟨Z, S, Ω, mZ, mS, mΩ, Q, (physical_valid_iff P Q ψ a b δ).mp hv,
      (physical_capped_iff P Q N).mp hc⟩
  · rintro ⟨Z, S, Ω, mZ, mS, mΩ, Q, hv, hc⟩
    let := mZ
    let := mS
    let := mΩ
    exact ⟨Z, S, Ω, mZ, mS, mΩ, Q, (physical_valid_iff P Q ψ a b δ).mpr hv,
      (physical_capped_iff P Q N).mpr hc⟩

theorem maximumBudget_eq (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    maximumBudget.{u} P ψ a b δ = ProductBudget.maximumBudget.{u} (ψ.reindex (fixedBlockIndexEquiv P)) a b δ := by
  have he : capFeasible.{u} P ψ a b δ =
      ProductBudget.capFeasible.{u} (ψ.reindex (fixedBlockIndexEquiv P)) a b δ :=
    funext (fun N => propext (capFeasible_iff P ψ a b δ N))
  unfold maximumBudget ProductBudget.maximumBudget
  rw [he]

theorem expectedBudget_le_maximumBudget (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    expectedBudget.{u} P ψ a b δ ≤ ENat.toENNReal (maximumBudget.{u} P ψ a b δ) := by
  rw [expectedBudget_eq, maximumBudget_eq]
  exact ProductBudget.expectedBudget_le_maximumBudget _ a b δ

theorem budget_transport (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    expectedBudget.{u} P ψ a b δ = ProductBudget.expectedBudget.{u} (ψ.reindex (fixedBlockIndexEquiv P)) a b δ ∧
    (∀ N, capFeasible.{u} P ψ a b δ N ↔ ProductBudget.capFeasible.{u} (ψ.reindex (fixedBlockIndexEquiv P)) a b δ N) ∧
    maximumBudget.{u} P ψ a b δ = ProductBudget.maximumBudget.{u} (ψ.reindex (fixedBlockIndexEquiv P)) a b δ :=
  ⟨expectedBudget_eq P ψ a b δ, capFeasible_iff P ψ a b δ, maximumBudget_eq P ψ a b δ⟩

end LocalCertification.Protocol.MeasurableExecution.FixedBlock
