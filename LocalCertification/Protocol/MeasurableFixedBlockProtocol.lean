import LocalCertification.Quantum.MeasurablePOVMReindex
import LocalCertification.Protocol.MeasurableExecutionProduct
import LocalCertification.Quantum.FixedBlockMeasurement

/-! General fixed-block physical execution. The prescribed partition is fixed
outside the action space. Within each block the original POVM is arbitrary;
only the product across the prescribed blocks is imposed. -/
set_option autoImplicit false
open MeasureTheory LocalCertification.Quantum CertificationGaussian
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.FixedBlock
universe u
variable {k m : ℕ} {Z S : Type u} {Ω : Fin m → Type u}
  [MeasurableSpace Z] [MeasurableSpace S] [∀ i, MeasurableSpace (Ω i)]

def physical (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω) :
    BornProtocol Z S ((i : Fin m) → Ω i) (QuditIndex 2 (k*m)) where
  toRawProtocol := Q.toRawProtocol
  measurements := (POVMKernel.product Q.localFamilies).reindexHilbert (fixedBlockIndexEquiv P).symm

theorem physical_raw (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω) :
    (physical P Q).toRawProtocol = Q.toRawProtocol := rfl

theorem physical_measurement_apply (P : FixedBlockPartition k m)
    (Q : ProductProtocol (2^k) m Z S Ω) (s : S) (A : Set ((i : Fin m) → Ω i)) :
    ((physical P Q).measurements.measurement s).toVectorMeasure A =
      ((MeasurablePOVM.product (fun i => (Q.localFamilies i).measurement s)).toVectorMeasure A).submatrix
        (fixedBlockIndexEquiv P) (fixedBlockIndexEquiv P) := rfl

theorem physical_bornKernel (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    (physical P Q).measurements.bornKernel ρ =
      Q.toBorn.measurements.bornKernel (ρ.reindex (fixedBlockIndexEquiv P)) :=
  POVMKernel.bornKernel_reindexHilbert_input (POVMKernel.product Q.localFamilies)
    (fixedBlockIndexEquiv P).symm ρ

theorem physical_kernel (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) (t : ℕ) :
    (physical P Q).kernel ρ t = Q.toBorn.kernel (ρ.reindex (fixedBlockIndexEquiv P)) t := by
  change stoppedKernel Q.toRawRules ((physical P Q).measurements.bornKernel ρ) t =
    stoppedKernel Q.toRawRules (Q.toBorn.measurements.bornKernel (ρ.reindex (fixedBlockIndexEquiv P))) t
  rw [physical_bornKernel]

theorem physical_law (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    (physical P Q).law ρ = Q.toBorn.law (ρ.reindex (fixedBlockIndexEquiv P)) := by
  change stoppedLaw Q.toRawRules Q.seedLaw ((physical P Q).measurements.bornKernel ρ) =
    stoppedLaw Q.toRawRules Q.seedLaw (Q.toBorn.measurements.bornKernel (ρ.reindex (fixedBlockIndexEquiv P)))
  congr 1
  exact physical_bornKernel P Q ρ

theorem physical_prefix (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) (t : ℕ) :
    ((physical P Q).law ρ).map (rawPrefix t) =
      (Q.toBorn.law (ρ.reindex (fixedBlockIndexEquiv P))).map (rawPrefix t) := by
  rw [physical_law]

theorem physical_time (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (p : Sample Z (Slot ((i : Fin m) → Ω i))) : (physical P Q).time p = Q.toBorn.time p := rfl

theorem physical_decision (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (p : Sample Z (Slot ((i : Fin m) → Ω i))) :
    (physical P Q).reportedDecision p = Q.toBorn.reportedDecision p := rfl

theorem physical_cost (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (p : Sample Z (Slot ((i : Fin m) → Ω i))) : (physical P Q).copyCost p = Q.toBorn.copyCost p := rfl

theorem physical_fullRecord (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (p : Sample Z (Slot ((i : Fin m) → Ω i))) :
    fullRecordSample (physical P Q).toRawRules p = fullRecordSample Q.toRawRules p := rfl

theorem physical_legal_iff (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (p : Sample Z (Slot ((i : Fin m) → Ω i))) :
    Legal (physical P Q).toRawRules p ↔ Legal Q.toRawRules p := Iff.rfl

theorem physical_capped_iff (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (N : ℕ) : (physical P Q).Capped N ↔ Q.toBorn.Capped N := Iff.rfl

theorem physical_expectedCopies (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    (physical P Q).expectedCopies ρ = Q.toBorn.expectedCopies (ρ.reindex (fixedBlockIndexEquiv P)) := by
  change (∫⁻ p, Q.toBorn.copyCost p ∂(physical P Q).law ρ) =
    ∫⁻ p, Q.toBorn.copyCost p ∂Q.toBorn.law (ρ.reindex (fixedBlockIndexEquiv P))
  rw [physical_law]

theorem physical_terminates_iff (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    (physical P Q).Terminates ρ ↔ Q.toBorn.Terminates (ρ.reindex (fixedBlockIndexEquiv P)) := by
  change (∀ᵐ p ∂(physical P Q).law ρ, Q.toBorn.time p ≠ ⊤) ↔
    ∀ᵐ p ∂Q.toBorn.law (ρ.reindex (fixedBlockIndexEquiv P)), Q.toBorn.time p ≠ ⊤
  rw [physical_law]

theorem physical_valid_iff (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω)
    (ψ : QIT.PureVector (QuditIndex 2 (k*m))) (a b δ : ℝ) :
    (physical P Q).Valid ψ a b δ ↔ Q.toBorn.Valid (ψ.reindex (fixedBlockIndexEquiv P)) a b δ := by
  have hworld (ρ : QIT.State (QuditIndex 2 (k*m))) (j : Fin 2) :
      ((physical P Q).Terminates ρ ∧
        (physical P Q).law ρ {p | (physical P Q).reportedDecision p = j} ≤ ENNReal.ofReal δ) ↔
      (Q.toBorn.Terminates (ρ.reindex (fixedBlockIndexEquiv P)) ∧
        Q.toBorn.law (ρ.reindex (fixedBlockIndexEquiv P)) {p | Q.toBorn.reportedDecision p = j} ≤
          ENNReal.ofReal δ) := by
    rw [physical_terminates_iff, physical_law]
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
      apply (hworld ρ 1).mpr
      exact h.1 (ρ.reindex (fixedBlockIndexEquiv P)) (by rwa [pureTargetFidelity_reindex])
    · intro ρ hρ
      apply (hworld ρ 0).mpr
      exact h.2 (ρ.reindex (fixedBlockIndexEquiv P)) (by rwa [pureTargetFidelity_reindex])

theorem exists_physical_execution (P : FixedBlockPartition k m) (Q : ProductProtocol (2^k) m Z S Ω) :
    ∃ R : BornProtocol Z S ((i : Fin m) → Ω i) (QuditIndex 2 (k*m)),
      R.toRawProtocol = Q.toRawProtocol ∧
      (∀ s A, (R.measurements.measurement s).toVectorMeasure A =
        ((MeasurablePOVM.product (fun i => (Q.localFamilies i).measurement s)).toVectorMeasure A).submatrix
          (fixedBlockIndexEquiv P) (fixedBlockIndexEquiv P)) ∧
      (∀ ρ, R.law ρ = Q.toBorn.law (ρ.reindex (fixedBlockIndexEquiv P))) ∧
      (∀ ρ t, (R.law ρ).map (rawPrefix t) =
        (Q.toBorn.law (ρ.reindex (fixedBlockIndexEquiv P))).map (rawPrefix t)) ∧
      (∀ p, R.time p = Q.toBorn.time p ∧ R.reportedDecision p = Q.toBorn.reportedDecision p ∧
        R.copyCost p = Q.toBorn.copyCost p ∧
        fullRecordSample R.toRawRules p = fullRecordSample Q.toRawRules p ∧
        (Legal R.toRawRules p ↔ Legal Q.toRawRules p)) ∧
      (∀ ρ, R.expectedCopies ρ = Q.toBorn.expectedCopies (ρ.reindex (fixedBlockIndexEquiv P))) ∧
      (∀ N, R.Capped N ↔ Q.toBorn.Capped N) ∧
      (∀ ψ a b δ, R.Valid ψ a b δ ↔
        Q.toBorn.Valid (ψ.reindex (fixedBlockIndexEquiv P)) a b δ) :=
  ⟨physical P Q, rfl, physical_measurement_apply P Q, physical_law P Q, physical_prefix P Q,
    fun _ => ⟨rfl, rfl, rfl, rfl, Iff.rfl⟩, physical_expectedCopies P Q,
    physical_capped_iff P Q, physical_valid_iff P Q⟩

end LocalCertification.Protocol.MeasurableExecution.FixedBlock
