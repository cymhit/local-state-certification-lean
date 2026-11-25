import LocalCertification.Protocol.TrajectoryEncoding
import LocalCertification.Protocol.TrajectoryCost

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- The original executor's actual Born kernel, padded only after it has stopped. -/
def executionSlotKernel (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    Kernel (SlotHistory Z (CertificationGaussian.QuditIndex d n) m) (Option (CertificationGaussian.QuditIndex d n)) :=
  stopContinue (activePrefix P.toRawRules m) (activePrefix_measurable P.toRawRules m)
    (controlledProductBornKernel d n ρ (prefixSetting P.toRawRules m) (prefixSetting_measurable P.toRawRules m))

instance executionSlotKernel_markov (P : QuditProtocol Z d n)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) : IsMarkovKernel (executionSlotKernel P ρ m) := by
  unfold executionSlotKernel
  infer_instance

/-- The genuine infinite execution law on the original seed and padded outcome stream. -/
def executionLaw (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    Measure (RawSample Z (CertificationGaussian.QuditIndex d n)) := rawTrajectoryLaw P.seedLaw (executionSlotKernel P ρ)

instance executionLaw_probability (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    IsProbabilityMeasure (executionLaw P ρ) := by
  unfold executionLaw
  infer_instance

/-- Infinite and finite physical executions agree on every original prefix. -/
theorem executionLaw_prefix (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    (executionLaw P ρ).map (rawPrefix m) = executionPrefixLaw P ρ m :=
  rawTrajectoryLaw_prefix P.seedLaw (executionSlotKernel P ρ) m

/-- One common probability-one set supports all causal consistency conditions. -/
theorem executionLaw_ae_consistent (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    ∀ᵐ p ∂executionLaw P ρ, ∀ m, ConsistentPrefix P.toRawRules m (rawPrefix m p) := by
  rw [ae_all_iff]
  intro m
  have h := executionPrefixLaw_ae_consistent P ρ m
  rw [← executionLaw_prefix] at h
  exact (ae_map_iff (rawPrefix_measurable m).aemeasurable (consistentPrefix_measurable P.toRawRules m)).mp h

def executionTime (P : QuditProtocol Z d n) (p : RawSample Z (CertificationGaussian.QuditIndex d n)) : WithTop ℕ :=
  stoppingTime P.toRawRules p.1 (fun m => (p.2 m).getD default)

def executionDecision (P : QuditProtocol Z d n) (p : RawSample Z (CertificationGaussian.QuditIndex d n)) : Fin 2 :=
  terminalDecision P.toRawRules p.1 (fun m => (p.2 m).getD default)

def executionCost (P : QuditProtocol Z d n) (p : RawSample Z (CertificationGaussian.QuditIndex d n)) : ℝ≥0∞ :=
  ENat.toENNReal (executionTime P p)

theorem executionTime_measurable (P : QuditProtocol Z d n) : Measurable (executionTime P) :=
  (stoppingTime_measurable P.toRawRules).comp (measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun m => (measurable_of_countable (fun o : Option (CertificationGaussian.QuditIndex d n) => o.getD default)).comp
      ((measurable_pi_apply m).comp measurable_snd))))

theorem executionDecision_measurable (P : QuditProtocol Z d n) : Measurable (executionDecision P) :=
  (terminalDecision_measurable P.toRawRules).comp (measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun m => (measurable_of_countable (fun o : Option (CertificationGaussian.QuditIndex d n) => o.getD default)).comp
      ((measurable_pi_apply m).comp measurable_snd))))

theorem executionCost_measurable (P : QuditProtocol Z d n) : Measurable (executionCost P) :=
  (measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t)).comp (executionTime_measurable P)

/-- Extended expected copy cost; it is not assumed finite even for valid protocols. -/
def expectedCopies (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : ℝ≥0∞ :=
  ∫⁻ p, executionCost P p ∂executionLaw P ρ

/-- Exact physical E(T∧m) identity on the literal seed/slot execution space. -/
theorem execution_expected_min (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (m : ℕ) :
    (∫⁻ h, prefixActiveCount (activePrefix P.toRawRules) m h ∂executionPrefixLaw P ρ m) =
      ∫⁻ p, min (executionCost P p) (m : ℝ≥0∞) ∂executionLaw P ρ := by
  change _ = ∫⁻ p, min (executionCost P p) (m : ℝ≥0∞)
    ∂((trajectoryLaw P.seedLaw (executionSlotKernel P ρ)).map unpackTrajectory)
  rw [lintegral_map ((executionCost_measurable P).min measurable_const) unpackTrajectory_measurable]
  exact stoppedTrajectory_expected_min P.toRawRules P.seedLaw
    (fun t => controlledProductBornKernel d n ρ (prefixSetting P.toRawRules t)
      (prefixSetting_measurable P.toRawRules t)) m

/-- Monotone convergence holds in the actual physical input world, including infinite cost. -/
theorem execution_expected_truncations (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (⨆ m : ℕ, ∫⁻ p, min (executionCost P p) (m : ℝ≥0∞) ∂executionLaw P ρ) = expectedCopies P ρ := by
  rw [← lintegral_iSup (fun m => (executionCost_measurable P).min measurable_const)
    (fun a b hab p => min_le_min_left _ (Nat.cast_le.mpr hab))]
  simp only [ennreal_iSup_min_nat, expectedCopies]

/-- The actual two-world physical finite-prefix information bound by genuine truncated stopping time. -/
theorem execution_klDiv_le_truncated_cost (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) (m : ℕ) :
    klDiv (executionPrefixLaw P ρ m) (executionPrefixLaw P σ m) ≤
      L * ∫⁻ p, min (executionCost P p) (m : ℝ≥0∞) ∂executionLaw P ρ := by
  rw [← execution_expected_min]
  exact executionPrefixLaw_klDiv_le P ρ σ L hL m

/-- Uniform finite-prefix information bound by the real expected stopping cost, with no AC or finiteness assumption. -/
theorem execution_klDiv_le_expected (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) (m : ℕ) :
    klDiv (executionPrefixLaw P ρ m) (executionPrefixLaw P σ m) ≤ L * expectedCopies P ρ := by
  refine (execution_klDiv_le_truncated_cost P ρ σ L hL m).trans ?_
  unfold expectedCopies
  gcongr with p
  exact min_le_left _ _

/-- Almost-sure termination is imposed separately under each promised physical input. -/
def Terminates (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : Prop :=
  ∀ᵐ p ∂executionLaw P ρ, executionTime P p ≠ ⊤

/-- Decision 0 accepts high fidelity. Errors are averaged over the common seed and actual Born outcomes.
No finite expectation or off-promise termination condition is included. -/
def Valid (P : QuditProtocol Z d n) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ) : Prop :=
  (∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), a ≤ pureTargetFidelity ψ ρ →
    Terminates P ρ ∧ executionLaw P ρ {p | executionDecision P p = 1} ≤ ENNReal.ofReal δ) ∧
  (∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), pureTargetFidelity ψ ρ ≤ b →
    Terminates P ρ ∧ executionLaw P ρ {p | executionDecision P p = 0} ≤ ENNReal.ofReal δ)

/-- Every-path caps keep all seeds and all outcome branches; they are stronger than almost-sure bounds. -/
def Capped (P : QuditProtocol Z d n) (N : ℕ) : Prop := EveryPathCap P.toRawRules N

theorem executionTime_le_of_capped (P : QuditProtocol Z d n) (N : ℕ) (hN : Capped P N)
    (p : RawSample Z (CertificationGaussian.QuditIndex d n)) : executionTime P p ≤ (N : WithTop ℕ) :=
  (everyPathCap_iff_stoppingTime_le P.toRawRules N).mp hN p.1 (fun m => (p.2 m).getD default)

theorem expectedCopies_le_of_capped (P : QuditProtocol Z d n) (N : ℕ) (hN : Capped P N)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : expectedCopies P ρ ≤ (N : ℝ≥0∞) := by
  have hp (p : RawSample Z (CertificationGaussian.QuditIndex d n)) : executionCost P p ≤ (N : ℝ≥0∞) := by
    have h : (show ℕ∞ from executionTime P p) ≤ (N : ℕ∞) := executionTime_le_of_capped P N hN p
    exact ENat.toENNReal_le.mpr h
  have h := lintegral_mono hp (μ := executionLaw P ρ)
  simpa only [lintegral_const, measure_univ, mul_one, expectedCopies] using h

end LocalCertification.Protocol
