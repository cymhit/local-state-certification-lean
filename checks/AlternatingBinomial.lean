import LocalCertification.Extremal.ElementaryDecay

set_option autoImplicit false

open Polynomial LocalCertification.Extremal
open scoped BigOperators

/-- Equation (S22) as an identity of real polynomials. -/
example (r : ℕ) :
    (∑ k ∈ Finset.range (r + 1), (-1 : ℝ)^k • binomialPolynomial k) =
      (-1 : ℝ)^r • (binomialPolynomial r).comp (X - 1) :=
  (decayPolynomial_eq_alternating_sum r).symm.trans (decayPolynomial_eq_shifted_binomial r)

example (r : ℕ) :
    (∑ k ∈ Finset.range (r + 1), (-1 : ℝ)^k • binomialPolynomial k).eval 0 = 1 := by
  rw [← decayPolynomial_eq_alternating_sum]
  exact (decayPolynomial_admissible r).2

example (r n : ℕ) :
    (∑ k ∈ Finset.range (r + 1), (-1 : ℝ)^k • binomialPolynomial k).eval
      ((n + 1 : ℕ) : ℝ) = (-1 : ℝ)^r * (n.choose r : ℝ) := by
  rw [← decayPolynomial_eq_alternating_sum]
  exact decayPolynomial_eval_positive r n

#eval IO.println "REGRESSION_CHECK\tAlternatingBinomial\tPASS"
