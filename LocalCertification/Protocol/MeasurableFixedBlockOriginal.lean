import LocalCertification.Protocol.MeasurableFixedBlockBudgets
import LocalCertification.Protocol.MeasurableExecutionUniverse

/-! Literal fixed-block protocols with independent seed, setting and outcome
universes. Bijective alignment preserves the original labels and null paths;
the fixed physical partition changes only the Hilbert-coordinate matrix. -/
set_option autoImplicit false
open MeasureTheory LocalCertification.Quantum CertificationGaussian
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.FixedBlock
universe u v w
variable {k m : ℕ} {Z : Type u} {S : Type v} {Ω : Fin m → Type w}
  [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]

theorem local_family_coverage {H Ξ : Type*} [MeasurableSpace H] [MeasurableSpace Ξ]
    (K : POVMKernel H Ξ (Fin k → Fin 2)) :
    ∃ L : POVMKernel H Ξ (Fin (2^k)), L.reindexHilbert (blockLabelEquiv k).symm = K :=
  ⟨K.reindexHilbert (blockLabelEquiv k), K.reindexHilbert_inverse (blockLabelEquiv k)⟩

namespace Original

def law (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) : Measure (OriginalProductProtocol.LiteralSample Z Ω) :=
  ((physical P Q.aligned).law ρ).map (OriginalProductProtocol.sampleEquiv.{u,v,w}).symm

theorem law_eq (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    law P Q ρ = Q.law (ρ.reindex (fixedBlockIndexEquiv P)) := by
  unfold law
  rw [physical_law]
  rfl

instance law_probability (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) : IsProbabilityMeasure (law P Q ρ) := by
  rw [law_eq]
  infer_instance

theorem physical_kernel_original (P : FixedBlockPartition k m)
    (Q : OriginalProductProtocol (2^k) m Z S Ω) (ρ : QIT.State (QuditIndex 2 (k*m))) (s : S) :
    (physical P Q.aligned).measurements.bornKernel ρ (ULift.up s) =
      (((MeasurablePOVM.product (fun i => (Q.localFamilies i).measurement s)).reindexHilbert
        (fixedBlockIndexEquiv P).symm).born ρ).map (fun x i => ULift.up (x i)) := by
  rw [physical_bornKernel, MeasurablePOVM.born_reindexHilbert_input]
  exact Q.aligned_kernel (ρ.reindex (fixedBlockIndexEquiv P)) s

theorem fullRecord (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (p : OriginalProductProtocol.LiteralSample Z Ω) :
    (OriginalProductProtocol.fullSampleEquiv.{u,v,w}).symm
      (fullRecordSample (physical P Q.aligned).toRawRules
        ((OriginalProductProtocol.sampleEquiv.{u,v,w}) p)) = Q.fullRecord p := rfl

theorem capped_iff (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (N : ℕ) : Q.Capped N ↔ (physical P Q.aligned).Capped N :=
  (Q.capped_iff N).symm.trans (physical_capped_iff P Q.aligned N).symm

def expectedCopies (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) : ℝ≥0∞ := ∫⁻ p, ENat.toENNReal (Q.time p) ∂law P Q ρ

theorem expectedCopies_eq_physical (P : FixedBlockPartition k m)
    (Q : OriginalProductProtocol (2^k) m Z S Ω) (ρ : QIT.State (QuditIndex 2 (k*m))) :
    expectedCopies P Q ρ = (physical P Q.aligned).expectedCopies ρ := by
  calc
    _ = Q.expectedCopies (ρ.reindex (fixedBlockIndexEquiv P)) := by
      unfold expectedCopies
      rw [law_eq]
      rfl
    _ = Q.aligned.toBorn.expectedCopies (ρ.reindex (fixedBlockIndexEquiv P)) :=
      Q.expectedCopies_eq_aligned _
    _ = _ := (physical_expectedCopies P Q.aligned ρ).symm

def Valid (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) : Prop :=
  (∀ ρ : QIT.State (QuditIndex 2 (k*m)), a ≤ pureTargetFidelity ψ ρ →
    (∀ᵐ p ∂law P Q ρ, Q.time p ≠ ⊤) ∧ law P Q ρ {p | Q.reportedDecision p = 1} ≤ ENNReal.ofReal δ) ∧
  (∀ ρ : QIT.State (QuditIndex 2 (k*m)), pureTargetFidelity ψ ρ ≤ b →
    (∀ᵐ p ∂law P Q ρ, Q.time p ≠ ⊤) ∧ law P Q ρ {p | Q.reportedDecision p = 0} ≤ ENNReal.ofReal δ)

theorem valid_iff_reindexed (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    Valid P Q ψ a b δ ↔ Q.Valid (ψ.reindex (fixedBlockIndexEquiv P)) a b δ := by
  have hworld (ρ : QIT.State (QuditIndex 2 (k*m))) (j : Fin 2) :
      ((∀ᵐ p ∂law P Q ρ, Q.time p ≠ ⊤) ∧
        law P Q ρ {p | Q.reportedDecision p = j} ≤ ENNReal.ofReal δ) ↔
      (Q.Terminates (ρ.reindex (fixedBlockIndexEquiv P)) ∧
        Q.law (ρ.reindex (fixedBlockIndexEquiv P)) {p | Q.reportedDecision p = j} ≤ ENNReal.ofReal δ) := by
    rw [law_eq]
    rfl
  constructor
  · intro h
    constructor
    · intro σ hσ
      obtain ⟨ρ, rfl⟩ := (stateReindexEquiv (fixedBlockIndexEquiv P)).surjective σ
      have hf : a ≤ pureTargetFidelity ψ ρ := by
        change a ≤ pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P))
          (ρ.reindex (fixedBlockIndexEquiv P)) at hσ
        rwa [pureTargetFidelity_reindex] at hσ
      exact (hworld ρ 1).mp (h.1 ρ hf)
    · intro σ hσ
      obtain ⟨ρ, rfl⟩ := (stateReindexEquiv (fixedBlockIndexEquiv P)).surjective σ
      have hf : pureTargetFidelity ψ ρ ≤ b := by
        change pureTargetFidelity (ψ.reindex (fixedBlockIndexEquiv P))
          (ρ.reindex (fixedBlockIndexEquiv P)) ≤ b at hσ
        rwa [pureTargetFidelity_reindex] at hσ
      exact (hworld ρ 0).mp (h.2 ρ hf)
  · intro h
    constructor
    · intro ρ hρ
      exact (hworld ρ 1).mpr (h.1 (ρ.reindex (fixedBlockIndexEquiv P)) (by rwa [pureTargetFidelity_reindex]))
    · intro ρ hρ
      exact (hworld ρ 0).mpr (h.2 (ρ.reindex (fixedBlockIndexEquiv P)) (by rwa [pureTargetFidelity_reindex]))

theorem valid_iff_physical (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    Valid P Q ψ a b δ ↔ (physical P Q.aligned).Valid ψ a b δ :=
  (valid_iff_reindexed P Q ψ a b δ).trans
    ((Q.valid_iff_aligned (ψ.reindex (fixedBlockIndexEquiv P)) a b δ).trans
      (physical_valid_iff P Q.aligned ψ a b δ).symm)

def protocolCost (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ ρ : {ρ : QIT.State (QuditIndex 2 (k*m)) // a ≤ pureTargetFidelity ψ ρ ∨ pureTargetFidelity ψ ρ ≤ b},
    expectedCopies P Q ρ.val

theorem protocolCost_eq_physical (P : FixedBlockPartition k m)
    (Q : OriginalProductProtocol (2^k) m Z S Ω) (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b : ℝ) :
    protocolCost P Q ψ a b = FixedBlock.protocolCost P Q.aligned ψ a b := by
  apply congrArg iSup
  funext ρ
  exact expectedCopies_eq_physical P Q ρ.val

theorem expectedBudget_le_cost (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) (hv : Valid P Q ψ a b δ) :
    FixedBlock.expectedBudget.{max u v w} P ψ a b δ ≤ protocolCost P Q ψ a b :=
  (expectedBudget_le_protocolCost P Q.aligned ψ a b δ ((valid_iff_physical P Q ψ a b δ).mp hv)).trans_eq
    (protocolCost_eq_physical P Q ψ a b).symm

theorem capFeasible_of_capped (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) (hv : Valid P Q ψ a b δ)
    (N : ℕ) (hc : Q.Capped N) : FixedBlock.capFeasible.{max u v w} P ψ a b δ N := by
  apply (FixedBlock.capFeasible_iff P ψ a b δ N).mpr
  exact ProductBudget.capFeasible_of_protocol Q.aligned (ψ.reindex (fixedBlockIndexEquiv P)) a b δ
    ((Q.valid_iff_aligned _ a b δ).mp ((valid_iff_reindexed P Q ψ a b δ).mp hv)) N ((Q.capped_iff N).mpr hc)

theorem maximumBudget_le_cap (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) (hv : Valid P Q ψ a b δ)
    (N : ℕ) (hc : Q.Capped N) : FixedBlock.maximumBudget.{max u v w} P ψ a b δ ≤ (N : ℕ∞) := by
  rw [FixedBlock.maximumBudget_eq]
  exact ProductBudget.maximumBudget_le_of_feasible _ a b δ N
    ((FixedBlock.capFeasible_iff P ψ a b δ N).mp (capFeasible_of_capped P Q ψ a b δ hv N hc))

end Original

theorem original_budget_transport (P : FixedBlockPartition k m) (Q : OriginalProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    (∀ ρ, Original.law P Q ρ = Q.law (ρ.reindex (fixedBlockIndexEquiv P))) ∧
    (∀ ρ, (∫⁻ p, ENat.toENNReal (Q.time p) ∂Original.law P Q ρ) =
      (physical P Q.aligned).expectedCopies ρ) ∧
    (∀ N : ℕ, (∀ p, Q.Legal p → Q.time p ≤ (N : ℕ∞)) ↔ (physical P Q.aligned).Capped N) ∧
    (∀ p, (OriginalProductProtocol.fullSampleEquiv.{u,v,w}).symm
      (fullRecordSample (physical P Q.aligned).toRawRules
        ((OriginalProductProtocol.sampleEquiv.{u,v,w}) p)) = Q.fullRecord p) ∧
    (Original.Valid P Q ψ a b δ →
      expectedBudget.{max u v w} P ψ a b δ ≤
        ⨆ ρ : {ρ : QIT.State (QuditIndex 2 (k*m)) // a ≤ pureTargetFidelity ψ ρ ∨ pureTargetFidelity ψ ρ ≤ b},
          ∫⁻ p, ENat.toENNReal (Q.time p) ∂Original.law P Q ρ.val ∧
      ∀ N : ℕ, Q.Capped N → capFeasible.{max u v w} P ψ a b δ N ∧
        maximumBudget.{max u v w} P ψ a b δ ≤ (N : ℕ∞)) :=
  ⟨Original.law_eq P Q, Original.expectedCopies_eq_physical P Q, Original.capped_iff P Q,
    Original.fullRecord P Q, fun hv => ⟨Original.expectedBudget_le_cost P Q ψ a b δ hv,
      fun N hc => ⟨Original.capFeasible_of_capped P Q ψ a b δ hv N hc,
        Original.maximumBudget_le_cap P Q ψ a b δ hv N hc⟩⟩⟩

end LocalCertification.Protocol.MeasurableExecution.FixedBlock
