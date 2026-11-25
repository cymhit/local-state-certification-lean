import LocalCertification.Quantum.FixedBlockMeasurement
import LocalCertification.Protocol.Budgets

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Quantum CertificationGaussian LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {k m : ℕ}

/-- Complete basis choices on the prescribed blocks and all their outcome labels.
The seed is arbitrary; the fixed partition is not an action and cannot be changed by the rules. -/
abbrev FixedBlockProtocol (Z : Type u) [MeasurableSpace Z] (k m : ℕ) :=
  RawProtocol Z (ProductSetting (2^k) m) (QuditIndex (2^k) m)

/-- The kernel is built from the actual physical km-qubit Born measure. -/
def fixedBlockBornKernel (P : FixedBlockPartition k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    Kernel (ProductSetting (2^k) m) (QuditIndex (2^k) m) where
  toFun U := fixedBlockBornMeasure P U ρ
  measurable' := by
    have he : (fun U => fixedBlockBornMeasure P U ρ)=
        (productBornKernel (2^k) m (ρ.reindex (fixedBlockIndexEquiv P))) := by
      funext U
      exact fixedBlockBornMeasure_eq P U ρ
    rw [he]
    exact (productBornKernel (2^k) m (ρ.reindex (fixedBlockIndexEquiv P))).measurable

theorem fixedBlockBornKernel_eq (P : FixedBlockPartition k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    fixedBlockBornKernel P ρ=productBornKernel (2^k) m (ρ.reindex (fixedBlockIndexEquiv P)) := by
  ext U s
  exact congrArg (fun μ : Measure (QuditIndex (2^k) m) => μ s) (fixedBlockBornMeasure_eq P U ρ)

instance fixedBlockBornKernel_markov (P : FixedBlockPartition k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) : IsMarkovKernel (fixedBlockBornKernel P ρ) := by
  rw [fixedBlockBornKernel_eq]
  infer_instance

variable {Z : Type u} [MeasurableSpace Z]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- The physical block Born draw is padded only after the actual common rules stop. -/
def fixedBlockSlotKernel (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) (t : ℕ) :
    Kernel (SlotHistory Z (QuditIndex (2^k) m) t) (Option (QuditIndex (2^k) m)) :=
  stopContinue (activePrefix Q.toRawRules t) (activePrefix_measurable Q.toRawRules t)
    ((fixedBlockBornKernel P ρ).comap (prefixSetting Q.toRawRules t) (prefixSetting_measurable Q.toRawRules t))

theorem fixedBlockSlotKernel_eq (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) (t : ℕ) :
    fixedBlockSlotKernel P Q ρ t=executionSlotKernel Q (ρ.reindex (fixedBlockIndexEquiv P)) t := by
  simp only [fixedBlockSlotKernel,fixedBlockBornKernel_eq,executionSlotKernel,controlledProductBornKernel]

instance fixedBlockSlotKernel_markov (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) (t : ℕ) : IsMarkovKernel (fixedBlockSlotKernel P Q ρ t) := by
  rw [fixedBlockSlotKernel_eq]
  infer_instance

/-- The actual physical infinite execution, retaining the unchanged arbitrary seed and complete record stream. -/
def fixedBlockExecutionLaw (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) : Measure (RawSample Z (QuditIndex (2^k) m)) :=
  rawTrajectoryLaw Q.seedLaw (fixedBlockSlotKernel P Q ρ)

/-- Equality of whole execution measures follows from equality of the actual physical Born kernels. -/
theorem fixedBlockExecutionLaw_eq (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    fixedBlockExecutionLaw P Q ρ=executionLaw Q (ρ.reindex (fixedBlockIndexEquiv P)) := by
  unfold fixedBlockExecutionLaw executionLaw
  congr 1
  funext t
  exact fixedBlockSlotKernel_eq P Q ρ t

/-- Every full public-record event retains its physical probability. -/
theorem fixedBlockExecutionLaw_full_records (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) (A : Set (RawSample Z (QuditIndex (2^k) m))) :
    fixedBlockExecutionLaw P Q ρ A=executionLaw Q (ρ.reindex (fixedBlockIndexEquiv P)) A := by
  rw [fixedBlockExecutionLaw_eq]

/-- Every path, including null branches and all seeds, has the identical stopping-time cap. -/
theorem fixedBlock_all_path_cap (Q : FixedBlockProtocol Z k m) (N : ℕ) :
    EveryPathCap Q.toRawRules N ↔ Capped Q N := Iff.rfl

/-- Physical expected copies are defined by the actual physical execution and its original stopping time. -/
def fixedBlockExpectedCopies (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) : ℝ≥0∞ :=
  ∫⁻ z,executionCost Q z ∂fixedBlockExecutionLaw P Q ρ

theorem fixedBlockExpectedCopies_eq (P : FixedBlockPartition k m) (Q : FixedBlockProtocol Z k m)
    (ρ : QIT.State (QuditIndex 2 (k*m))) :
    fixedBlockExpectedCopies P Q ρ=expectedCopies Q (ρ.reindex (fixedBlockIndexEquiv P)) := by
  rw [fixedBlockExpectedCopies,fixedBlockExecutionLaw_eq]
  rfl

end LocalCertification.Protocol
