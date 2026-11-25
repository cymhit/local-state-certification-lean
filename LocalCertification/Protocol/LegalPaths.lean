import LocalCertification.Protocol.TreeFullRecord

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {Z : Type u} {S : Type v} {O : Type w}
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace O]
    [Inhabited S] [Inhabited O] [Fintype O] [MeasurableSingletonClass O]

/-- Legal paths impose every causal slot consistency condition, with all seeds and branches retained. -/
def legalPaths (R : RawRules Z S O) : Set (RawSample Z O) :=
  {p | ∀ m, ConsistentPrefix R m (rawPrefix m p)}

omit [MeasurableSingletonClass O] in
theorem legalPaths_measurable (R : RawRules Z S O) : MeasurableSet (legalPaths R) := by
  have hm (m : ℕ) : MeasurableSet {p : RawSample Z O | ConsistentPrefix R m (rawPrefix m p)} :=
    (consistentPrefix_measurable R m).preimage (rawPrefix_measurable m)
  simpa only [legalPaths, Set.ofPred_forall] using MeasurableSet.iInter hm

omit [Fintype O] [MeasurableSingletonClass O] in
/-- Every point of the legal subtype reconstructs its unique original seed and a single completed logical stream. -/
theorem legalPath_logicalPrefix (R : RawRules Z S O) (p : legalPaths R) (m : ℕ) :
    logicalPrefix R p.val.1 (fun k => (p.val.2 k).getD default) m = rawPrefix m p.val :=
  trajectoryPrefix_eq_logical R (packTrajectory p.val) p.property m

variable {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- The actual physical law on the measurable subtype of all legal paths. -/
def legalPathLaw (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    Measure (legalPaths P.toRawRules) := Measure.comap Subtype.val (executionLaw P ρ)

/-- Subtype inclusion recovers exactly the original execution law, not a completed or conditioned surrogate. -/
theorem legalPathLaw_map (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (legalPathLaw P ρ).map Subtype.val = executionLaw P ρ := by
  rw [legalPathLaw, map_comap_subtype_coe (legalPaths_measurable P.toRawRules)]
  exact Measure.restrict_eq_self_of_ae_mem (executionLaw_ae_consistent P ρ)

instance legalPathLaw_probability (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    IsProbabilityMeasure (legalPathLaw P ρ) := by
  constructor
  have h := congrArg (fun μ => μ Set.univ) (legalPathLaw_map P ρ)
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ] at h
  simpa using h

/-- The expected-copy definition is unchanged on the original model's legal-path sample space. -/
theorem legalPathLaw_expectedCopies (P : QuditProtocol Z d n) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (∫⁻ p, executionCost P p.val ∂legalPathLaw P ρ) = expectedCopies P ρ := by
  unfold expectedCopies
  rw [← legalPathLaw_map, lintegral_map (executionCost_measurable P) measurable_subtype_coe]

end LocalCertification.Protocol
