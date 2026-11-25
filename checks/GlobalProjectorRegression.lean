import Lean
import LocalCertification.Comparisons.GlobalProjectorBorn
import LocalCertification.Comparisons.BoundedIIDTail
import LocalCertification.Comparisons.GlobalProjectorTest
set_option pp.universes true
set_option pp.proofs false
#check LocalCertification.Comparisons.target_projector_le_one
#print axioms LocalCertification.Comparisons.target_projector_le_one
#check LocalCertification.Comparisons.globalProjectorPOVM
#print axioms LocalCertification.Comparisons.globalProjectorPOVM
#check LocalCertification.Comparisons.globalProjectorPOVM_true
#print axioms LocalCertification.Comparisons.globalProjectorPOVM_true
#check LocalCertification.Comparisons.globalProjectorPOVM_false
#print axioms LocalCertification.Comparisons.globalProjectorPOVM_false
#check LocalCertification.Comparisons.globalProjector_prob_true
#print axioms LocalCertification.Comparisons.globalProjector_prob_true
#check LocalCertification.Comparisons.globalProjector_prob_false
#print axioms LocalCertification.Comparisons.globalProjector_prob_false
#check LocalCertification.Comparisons.globalProjectorParameter
#print axioms LocalCertification.Comparisons.globalProjectorParameter
#check LocalCertification.Comparisons.globalProjectorLaw
#print axioms LocalCertification.Comparisons.globalProjectorLaw
#check LocalCertification.Comparisons.globalProjectorLaw_probability
#print axioms LocalCertification.Comparisons.globalProjectorLaw_probability
#check LocalCertification.Comparisons.globalProjectorLaw_eq_bernoulli
#print axioms LocalCertification.Comparisons.globalProjectorLaw_eq_bernoulli
#check LocalCertification.Comparisons.projectorOutcome
#print axioms LocalCertification.Comparisons.projectorOutcome
#check LocalCertification.Comparisons.projectorOutcome_mem
#print axioms LocalCertification.Comparisons.projectorOutcome_mem
#check LocalCertification.Comparisons.globalProjector_integral
#print axioms LocalCertification.Comparisons.globalProjector_integral
#check LocalCertification.Comparisons.globalProjectorRecordLaw
#print axioms LocalCertification.Comparisons.globalProjectorRecordLaw
#check LocalCertification.Comparisons.globalProjector_iid
#print axioms LocalCertification.Comparisons.globalProjector_iid
#check LocalCertification.Comparisons.globalProjector_marginal
#print axioms LocalCertification.Comparisons.globalProjector_marginal
#check LocalCertification.Comparisons.iid_bounded_upper_tail
#print axioms LocalCertification.Comparisons.iid_bounded_upper_tail
#check LocalCertification.Comparisons.bounded_integrable
#print axioms LocalCertification.Comparisons.bounded_integrable
#check LocalCertification.Comparisons.iid_bounded_lower_tail
#print axioms LocalCertification.Comparisons.iid_bounded_lower_tail
#check LocalCertification.Comparisons.globalProjectorCopies
#print axioms LocalCertification.Comparisons.globalProjectorCopies
#check LocalCertification.Comparisons.globalProjectorMean
#print axioms LocalCertification.Comparisons.globalProjectorMean
#check LocalCertification.Comparisons.globalProjectorTest
#print axioms LocalCertification.Comparisons.globalProjectorTest
#check LocalCertification.Comparisons.globalProjectorTest_measurable
#print axioms LocalCertification.Comparisons.globalProjectorTest_measurable
#check LocalCertification.Comparisons.globalProjectorCopies_pos
#print axioms LocalCertification.Comparisons.globalProjectorCopies_pos
#check LocalCertification.Comparisons.globalProjectorCopies_confidence
#print axioms LocalCertification.Comparisons.globalProjectorCopies_confidence
#check LocalCertification.Comparisons.globalProjectorCopies_rounding
#print axioms LocalCertification.Comparisons.globalProjectorCopies_rounding
#check LocalCertification.Comparisons.globalProjectorCopies_upper
#print axioms LocalCertification.Comparisons.globalProjectorCopies_upper
#check LocalCertification.Comparisons.globalProjector_error_high
#print axioms LocalCertification.Comparisons.globalProjector_error_high
#check LocalCertification.Comparisons.globalProjector_error_low
#print axioms LocalCertification.Comparisons.globalProjector_error_low
#check LocalCertification.Comparisons.global_projector_comparison
#print axioms LocalCertification.Comparisons.global_projector_comparison
example (ψ : QIT.PureVector (Fin 1)) (ρ : QIT.State (Fin 1)) :
    LocalCertification.Comparisons.globalProjectorRecordLaw ψ ρ (LocalCertification.Comparisons.globalProjectorCopies 1 (1/2) (1/4))
      {x | LocalCertification.Comparisons.globalProjectorTest 1 (1/2) x ≠ true} ≤ ENNReal.ofReal (1/4) := by
  by_cases h : 1 ≤ LocalCertification.Quantum.pureTargetFidelity ψ ρ
  · exact LocalCertification.Comparisons.globalProjector_error_high ψ ρ (by norm_num) (by norm_num) (by norm_num) h
  · have hρ : LocalCertification.Quantum.pureTargetFidelity ψ ρ = 1 := by
      have hm : ψ.state.matrix = 1 := by
        ext a b
        fin_cases a
        fin_cases b
        have ht := ψ.state.trace_eq_one
        simpa [Matrix.trace, Matrix.diag] using ht
      rw [LocalCertification.Quantum.pureTargetFidelity, hm, Matrix.one_mul, ρ.trace_eq_one]
      rfl
    exact False.elim (h hρ.ge)

open Lean Elab Command in
run_elab do
  logInfo "REGRESSION_CHECK\tGlobalProjectorRegression\tPASS"
