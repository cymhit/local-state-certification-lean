import LocalCertification.Protocol.BornTrajectory

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set LocalCertification.Information
open scoped ENNReal LocalCertification.Information
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- A genuine raw protocol with arbitrary original seed law, stopping before it requests any copy. -/
def immediateStopProtocol (ν : Measure Z) [IsProbabilityMeasure ν] (j : Fin 2) : QuditProtocol Z d n where
  toRawRules := {rule := fun _ _ => Sum.inl j, measurable_rule := fun _ => measurable_const}
  seedLaw := ν
  seed_probability := inferInstance

theorem immediateStop_capped (ν : Measure Z) [IsProbabilityMeasure ν] (j : Fin 2) :
    Capped (immediateStopProtocol (d := d) (n := n) ν j) 0 := by
  intro z x
  simp [runContinues, runState, logicalPrefix, execPrefix, initialState, immediateStopProtocol, actionContinues]

theorem immediateStop_time (ν : Measure Z) [IsProbabilityMeasure ν] (j : Fin 2)
    (p : RawSample Z (CertificationGaussian.QuditIndex d n)) : executionTime (immediateStopProtocol ν j) p = 0 :=
  le_antisymm (executionTime_le_of_capped _ 0 (immediateStop_capped ν j) p) bot_le

theorem immediateStop_decision (ν : Measure Z) [IsProbabilityMeasure ν] (j : Fin 2)
    (p : RawSample Z (CertificationGaussian.QuditIndex d n)) : executionDecision (immediateStopProtocol ν j) p = j := by
  have hs := immediateStop_capped (d := d) (n := n) ν j
  have h := terminalDecision_eq_of_stopped (immediateStopProtocol ν j).toRawRules p.1
    (fun m => (p.2 m).getD default) 0 (hs p.1 (fun m => (p.2 m).getD default))
  simpa only [executionDecision, runState, execPrefix, logicalPrefix, initialState, immediateStopProtocol,
    actionDecision, Sum.elim_inl, id_eq] using h

theorem immediateStop_expectedCopies (ν : Measure Z) [IsProbabilityMeasure ν] (j : Fin 2)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : expectedCopies (immediateStopProtocol ν j) ρ = 0 := by
  apply le_antisymm
  · simpa only [Nat.cast_zero] using expectedCopies_le_of_capped (immediateStopProtocol ν j) 0 (immediateStop_capped ν j) ρ
  · exact bot_le

theorem immediateStop_terminates (ν : Measure Z) [IsProbabilityMeasure ν] (j : Fin 2)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : Terminates (immediateStopProtocol ν j) ρ := by
  exact Filter.Eventually.of_forall (fun p => by rw [immediateStop_time]; exact WithTop.zero_ne_top)

end LocalCertification.Protocol
