import LocalCertification.Certificates.ExecutableTail

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Certificates.Consumers

/-- The executable array really represents the unnormalized degree-zero numerator. -/
theorem constant_array_polynomial : Polynomial.ofFn 1 (fun _ => (6 : ℚ)) = C 6 := by
  simp [Polynomial.ofFn_eq_sum_monomial]

/-- A complete exact certificate, consumed through the general soundness theorem:
finite node1/infinity, dual weights 3 and -2, actual prefix and both executable tail arrays. -/
theorem degree_zero_exact_certificate :
    realCandidate 0 (-1) (C 6) ∈ feasible 3 0 ∧
    extrapolation 0 (realCandidate 0 (-1) (C 6)) = extremalValue 3 0 ∧ gamma 3 0 = 1/3 := by
  have ht : tailCheck 3 ((-(-1 : ℚ)) • (C 6)) 1 := by
    simpa only [constant_array_polynomial, neg_neg, one_smul] using
      arrayTailCheck_sound 3 1 (fun _ => 6) 1 constant_array_passes
  have hpref : ∀ w ∈ Finset.Icc 1 1, |rationalCandidateValue 3 (-1) (C 6) w|≤1 := by
    simpa only [constant_array_polynomial] using
      arrayPrefixCheck_sound 3 (-1) 1 (fun _ => 6) 1 constant_array_prefix
  have hc := finite_rational_certificate_optimal 3 (by norm_num) 0 (-1) (by norm_num)
    (C 6) (by simp) 1 (by omega) ht hpref 2
    (![(0 : ℕ), ∞] : Fin 2 → OnePoint ℕ) (![3,-2] : Fin 2 → ℚ)
    (by norm_num [Fin.sum_univ_succ])
    (by intro j; fin_cases j; norm_num [rationalNodeMonomial, Fin.sum_univ_succ])
    (by norm_num [Fin.sum_univ_succ])
  norm_num at hc
  exact hc

/-- The same complete certificate identifies the unique normalized original-envelope minimizer. -/
theorem degree_zero_unique_optimizer :
    admissible 0 (1 : ℝ[X]) ∧ envelopeRatio 3 (1 : ℝ[X]) = gamma 3 0 ∧
      ∀ P : ℝ[X], admissible 0 P → envelopeRatio 3 P = gamma 3 0 → P=1 := by
  have h := rational_normalization_of_attainment 3 (by norm_num) 0 (-1) (C 6) (by simp)
    degree_zero_exact_certificate.1 degree_zero_exact_certificate.2.1
  norm_num [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul] at h
  exact h

end LocalCertification.Certificates.Consumers
