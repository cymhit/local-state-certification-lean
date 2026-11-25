import LocalCertification.Protocol.FixedBlockProtocol

set_option autoImplicit false
open MeasureTheory Set LocalCertification.Quantum CertificationGaussian
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {k m : ℕ} {Z : Type u} [MeasurableSpace Z]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- Termination is tested under each original physical input state. -/
def fixedBlockTerminates (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) : Prop :=
  ∀ᵐ z ∂fixedBlockExecutionLaw P Q ρ,executionTime Q z≠⊤

/-- Physical promise classes and both errors are quantified over every physical mixed state. -/
def fixedBlockValid (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) : Prop :=
  (∀ ρ : QIT.State (QuditIndex 2 (k*m)),a≤pureTargetFidelity ψ ρ →
    fixedBlockTerminates P Q ρ ∧ fixedBlockExecutionLaw P Q ρ {z | executionDecision Q z=1}≤ENNReal.ofReal δ) ∧
  (∀ ρ : QIT.State (QuditIndex 2 (k*m)),pureTargetFidelity ψ ρ≤b →
    fixedBlockTerminates P Q ρ ∧ fixedBlockExecutionLaw P Q ρ {z | executionDecision Q z=0}≤ENNReal.ofReal δ)

/-- The fixed physical partition preserves validity for every arbitrary seed/rule protocol, both ways. -/
theorem fixedBlockValid_iff (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    fixedBlockValid P Q ψ a b δ ↔ Valid Q (ψ.reindex (fixedBlockIndexEquiv P)) a b δ := by
  constructor
  · intro h
    constructor
    · intro σ hσ
      obtain ⟨ρ,rfl⟩ := (stateReindexEquiv (fixedBlockIndexEquiv P)).surjective σ
      have hf : a≤pureTargetFidelity ψ ρ := by simpa only [stateReindexEquiv,Equiv.coe_fn_mk,pureTargetFidelity_reindex] using hσ
      simpa only [fixedBlockTerminates,Terminates,fixedBlockExecutionLaw_eq,stateReindexEquiv,Equiv.coe_fn_mk] using h.1 ρ hf
    · intro σ hσ
      obtain ⟨ρ,rfl⟩ := (stateReindexEquiv (fixedBlockIndexEquiv P)).surjective σ
      have hf : pureTargetFidelity ψ ρ≤b := by simpa only [stateReindexEquiv,Equiv.coe_fn_mk,pureTargetFidelity_reindex] using hσ
      simpa only [fixedBlockTerminates,Terminates,fixedBlockExecutionLaw_eq,stateReindexEquiv,Equiv.coe_fn_mk] using h.2 ρ hf
  · intro h
    constructor
    · intro ρ hρ
      have hf : a≤pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P)) (ρ.reindex (fixedBlockIndexEquiv P)) := by
        rwa [pureTargetFidelity_reindex]
      simpa only [fixedBlockTerminates,Terminates,fixedBlockExecutionLaw_eq] using h.1 _ hf
    · intro ρ hρ
      have hf : pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P)) (ρ.reindex (fixedBlockIndexEquiv P))≤b := by
        rwa [pureTargetFidelity_reindex]
      simpa only [fixedBlockTerminates,Terminates,fixedBlockExecutionLaw_eq] using h.2 _ hf

/-- The worst-case physical expected cost ranges over precisely the two physical fidelity promises. -/
def fixedBlockProtocolCost (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ ρ : {ρ : QIT.State (QuditIndex 2 (k*m)) // a≤pureTargetFidelity ψ ρ ∨ pureTargetFidelity ψ ρ≤b},
    fixedBlockExpectedCopies P Q ρ.val

theorem fixedBlockProtocolCost_eq (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b : ℝ) :
    fixedBlockProtocolCost P Q ψ a b=protocolCost Q (ψ.reindex (fixedBlockIndexEquiv P)) a b := by
  unfold fixedBlockProtocolCost protocolCost
  apply le_antisymm
  · apply iSup_le
    intro ρ
    have hf : ρ.val.reindex (fixedBlockIndexEquiv P)∈promisedStates (ψ.reindex (fixedBlockIndexEquiv P)) a b := by
      simpa only [promisedStates,Set.mem_ofPred_eq,pureTargetFidelity_reindex] using ρ.property
    exact le_iSup_of_le ⟨ρ.val.reindex (fixedBlockIndexEquiv P),hf⟩ (fixedBlockExpectedCopies_eq P Q ρ.val).le
  · apply iSup_le
    intro σ
    obtain ⟨ρ,hρ⟩ := (stateReindexEquiv (fixedBlockIndexEquiv P)).surjective σ.val
    have hf : a≤pureTargetFidelity ψ ρ ∨ pureTargetFidelity ψ ρ≤b := by
      have h := σ.property
      rw [←hρ] at h
      simpa only [stateReindexEquiv,Equiv.coe_fn_mk,promisedStates,Set.mem_ofPred_eq,pureTargetFidelity_reindex] using h
    apply le_iSup_of_le ⟨ρ,hf⟩
    rw [fixedBlockExpectedCopies_eq]
    change expectedCopies Q σ.val≤expectedCopies Q ((stateReindexEquiv (fixedBlockIndexEquiv P)) ρ)
    rw [hρ]

/-- Physical expected budget: infimum over the complete canonical normalization of all original raw protocols. -/
def fixedBlockExpectedBudget (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) : ℝ≥0∞ :=
  ⨅ Q : CanonicalProtocol (2^k) m,⨅ (_ : fixedBlockValid P Q.toRaw ψ a b δ),
    fixedBlockProtocolCost P Q.toRaw ψ a b

/-- Exact budget equality follows from validity and cost transportation, not a restricted protocol class. -/
theorem fixedBlockExpectedBudget_eq (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    fixedBlockExpectedBudget P ψ a b δ=expectedBudget (ψ.reindex (fixedBlockIndexEquiv P)) a b δ := by
  simp only [fixedBlockExpectedBudget,expectedBudget,fixedBlockProtocolCost_eq,fixedBlockValid_iff]

def fixedBlockCapFeasible (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) (N : ℕ) : Prop :=
  ∃ Q : CanonicalProtocol (2^k) m,fixedBlockValid P Q.toRaw ψ a b δ ∧ EveryPathCap Q.toRaw.toRawRules N

theorem fixedBlockCapFeasible_iff (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) (N : ℕ) :
    fixedBlockCapFeasible P ψ a b δ N ↔ capFeasible (ψ.reindex (fixedBlockIndexEquiv P)) a b δ N := by
  simp only [fixedBlockCapFeasible,capFeasible,fixedBlockValid_iff,Capped]

/-- Least physical every-path cap, or infinity when no valid finite cap exists. -/
def fixedBlockMaximumBudget (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) : WithTop ℕ := by
  classical
  exact if h : ∃ N,fixedBlockCapFeasible P ψ a b δ N then (Nat.find h : WithTop ℕ) else ⊤

theorem fixedBlockMaximumBudget_eq (P : FixedBlockPartition k m)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    fixedBlockMaximumBudget P ψ a b δ=maximumBudget (ψ.reindex (fixedBlockIndexEquiv P)) a b δ := by
  have he : fixedBlockCapFeasible P ψ a b δ=capFeasible (ψ.reindex (fixedBlockIndexEquiv P)) a b δ :=
    funext (fun N => propext (fixedBlockCapFeasible_iff P ψ a b δ N))
  unfold fixedBlockMaximumBudget maximumBudget
  rw [he]

/-- Full-image canonical normalization covers any seed universe and preserves physical validity,
all path caps, and extended physical input costs simultaneously. -/
theorem fixedBlock_canonical_coverage (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m) :
    ∃ R : CanonicalProtocol (2^k) m,
      (∀ ψ a b δ,fixedBlockValid P R.toRaw ψ a b δ ↔ fixedBlockValid P Q ψ a b δ) ∧
      (∀ N,Capped R.toRaw N ↔ Capped Q N) ∧
      (∀ ρ,fixedBlockExpectedCopies P R.toRaw ρ=fixedBlockExpectedCopies P Q ρ) := by
  refine ⟨normalizeProtocol Q,?_,normalizeProtocol_capped_iff Q,?_⟩
  · intro ψ a b δ
    rw [fixedBlockValid_iff,fixedBlockValid_iff]
    exact normalizeProtocol_valid_iff Q _ a b δ
  · intro ρ
    rw [fixedBlockExpectedCopies_eq,fixedBlockExpectedCopies_eq]
    exact normalizeProtocol_expectedCopies Q _

end LocalCertification.Protocol
