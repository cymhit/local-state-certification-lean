import LocalCertification.Certificates.Examples.Degree4
import LocalCertification.Extremal.DimensionParameters

/-! # The qubit quartic interpolation bound -/

set_option autoImplicit false
open Polynomial
open scoped BigOperators
namespace LocalCertification.Manuscript

private def quarticNodes : Fin 6 → ℝ := ![0, 1, 2, 3, 4, 7]

private theorem quarticNodes_strictMono : StrictMono quarticNodes := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [quarticNodes] at *

private theorem quartic_barycentric_denominator (i : Fin 6) :
    Extremal.barycentricDenominator (n := 5) quarticNodes i =
      (![-168, 36, -20, 24, -72, 2520] : Fin 6 → ℝ) i := by
  have h : ∀ j : Fin 6, Finset.univ.erase j =
      ![{1, 2, 3, 4, 5}, {0, 2, 3, 4, 5}, {0, 1, 3, 4, 5},
        {0, 1, 2, 4, 5}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] j := by decide
  rw [Extremal.barycentricDenominator, h]
  fin_cases i <;> norm_num [quarticNodes, Finset.prod_insert]

/-- Vanishing of the fifth interpolation coefficient at the six integer nodes. -/
theorem quartic_interpolation (p : ℝ[X]) (hp : Extremal.admissible 4 p) :
    5 + 378 * weightedSample 2 p 2 + 945 * weightedSample 2 p 4 =
      70 * weightedSample 2 p 1 + 945 * weightedSample 2 p 3 + 729 * weightedSample 2 p 7 := by
  have h := Extremal.barycentric_sum_eq_zero (n := 5) quarticNodes quarticNodes_strictMono
    p (lt_of_le_of_lt hp.1 (by decide))
  simp_rw [quartic_barycentric_denominator] at h
  norm_num [Fin.sum_univ_succ, quarticNodes, hp.2, weightedSample] at h ⊢
  linarith

/-- The signed envelope inequalities and the resulting lower bound for *every* quartic. -/
theorem quartic_envelope_bound (p : ℝ[X]) (hp : Extremal.admissible 4 p) :
    (5 + 1739 * ell 2 p ≤ 5 + 1323 * ell 2 p) ∧
    (5 + 1323 * ell 2 p ≤ 1744 * u 2 p) ∧
    5 / 1744 ≤ Extremal.envelopeRatio 3 p := by
  have hl (k : ℕ) : ell 2 p ≤ weightedSample 2 p (k + 1) :=
    Extremal.lowerEnvelope_le (2 + 1) (by norm_num) p k
  have hu (k : ℕ) : weightedSample 2 p (k + 1) ≤ u 2 p :=
    Extremal.le_upperEnvelope (2 + 1) (by norm_num) p k
  have hz : ell 2 p ≤ 0 := (Extremal.envelope_zero_bounds (2 + 1) (by norm_num) p).1
  have h₁ : 5 + 1739 * ell 2 p ≤ 5 + 1323 * ell 2 p := by linarith
  have h₂ : 5 + 1323 * ell 2 p ≤ 1744 * u 2 p := by
    have h := quartic_interpolation p hp
    linarith [hl 1, hl 3, hu 0, hu 2, hu 6]
  refine ⟨h₁, h₂, ?_⟩
  rw [← show (2 : ℝ) + 1 = 3 by norm_num]
  change 5 / 1744 ≤ (u 2 p - ell 2 p) / (1 - ell 2 p)
  apply (le_div_iff₀ (by linarith : 0 < 1 - ell 2 p)).mpr
  linarith

private theorem quartic_candidate_upper : Extremal.gamma 3 4 ≤ 5 / 1744 := by
  let a := Certificates.Examples.Degree4.data.2.1
  let P := Polynomial.ofFn 5 a
  have hdeg : P.natDegree ≤ 4 := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (by decide : 0 < 5) a)
  have htail : Certificates.tailCheck 3 (-(-1 : ℚ) • P) 7 := by
    rw [← Certificates.oriented_ofFn]
    exact Certificates.arrayTailCheck_sound _ _ _ _ Certificates.Examples.Degree4.tail_passes
  have hprefix := Certificates.arrayPrefixCheck_sound _ _ _ _ _
    Certificates.Examples.Degree4.prefix_passes
  have hf := Certificates.finite_rational_feasible 3 (by norm_num) 4 (-1) (by norm_num)
    P hdeg 7 (by decide) htail hprefix
  have hq : (1 : ℝ) < 3 := by norm_num
  have hB := Extremal.extrapolation_le_extremalValue 3 hq 4 hf
  rw [Extremal.extrapolation_formula, Certificates.realCandidate_polynomial _ _ _ hdeg] at hB
  norm_num [Certificates.realCandidate, P, a, Certificates.Examples.Degree4.data,
    Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ] at hB
  rw [Extremal.gamma_eq_extremalValue 3 hq 4]
  apply (div_le_iff₀ (by linarith : 0 < 1 + Extremal.extremalValue 3 4)).mpr
  linarith

/-- The universal interpolation lower bound meets the rational candidate upper bound. -/
theorem qubit_quartic_exact : gamma 2 4 = 5 / 1744 := by
  have hq : (1 : ℝ) < 3 := by norm_num
  rw [gamma, show (2 : ℝ) + 1 = 3 by norm_num]
  apply le_antisymm
  · exact quartic_candidate_upper
  · apply le_csInf (Extremal.envelope_ratios_nonempty 3 4)
    rintro t ⟨p, hp, rfl⟩
    exact (quartic_envelope_bound p hp).2.2

end LocalCertification.Manuscript
