import LocalCertification.Asymptotic.RationalNumerator
import Mathlib.Analysis.Polynomial.Basic

open scoped BigOperators Topology
open Polynomial Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The actual numerator of the upper-bound candidate. -/
def upperNumerator (a : ℝ) (r : ℕ) : ℝ[X] := (1 - X ^ 2) * (C a - X) ^ (r - 1)

private theorem one_sub_X_sq_natDegree : (1 - X ^ 2 : ℝ[X]).natDegree = 2 := by
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by simp)]
  simp

private theorem one_sub_X_sq_leadingCoeff : (1 - X ^ 2 : ℝ[X]).leadingCoeff = -1 := by
  rw [Polynomial.leadingCoeff_sub_of_degree_lt' (by simp)]
  simp

private theorem C_sub_X_natDegree (a : ℝ) : (C a - X).natDegree = 1 := by
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by simp)]
  simp

private theorem C_sub_X_leadingCoeff (a : ℝ) : (C a - X).leadingCoeff = -1 := by
  have he : (C a - X : ℝ[X]) = -(X - C a) := by ring
  rw [he, leadingCoeff_neg, leadingCoeff_X_sub_C]

theorem upperNumerator_degree (a : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    (upperNumerator a r).natDegree = r + 1 := by
  have hp : (C a - X : ℝ[X]).leadingCoeff ^ (r - 1) ≠ 0 := by
    rw [C_sub_X_leadingCoeff]
    exact pow_ne_zero _ (by norm_num)
  unfold upperNumerator
  rw [Polynomial.natDegree_mul' (by rw [one_sub_X_sq_leadingCoeff, leadingCoeff_pow]; exact mul_ne_zero (by norm_num) hp),
    Polynomial.natDegree_pow' hp, one_sub_X_sq_natDegree, C_sub_X_natDegree, mul_one]
  omega

theorem upperNumerator_leadingCoeff (a : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    (upperNumerator a r).leadingCoeff = (-1) ^ r := by
  rw [upperNumerator, leadingCoeff_mul, leadingCoeff_pow, one_sub_X_sq_leadingCoeff,
    C_sub_X_leadingCoeff, ← pow_succ', Nat.sub_add_cancel hr]

@[simp] theorem upperNumerator_eval_zero (a : ℝ) (r : ℕ) :
    (upperNumerator a r).eval 0 = a ^ (r - 1) := by simp [upperNumerator]

private theorem upperDenominator_leadingCoeff (a : ℝ) (ha : a ≠ 0) (s : ℕ) :
    ((1 - C a * X : ℝ[X]) ^ s).leadingCoeff = (-a) ^ s := by
  rw [leadingCoeff_pow]
  have hdeg : (1 : ℝ[X]).degree < (C a * X).degree := by
    simpa using (Polynomial.degree_C_lt_degree_C_mul_X (b := (1 : ℝ)) ha)
  rw [leadingCoeff_sub_of_degree_lt' hdeg, leadingCoeff_mul_X, leadingCoeff_C]

private theorem upperDenominator_natDegree (a : ℝ) (ha : a ≠ 0) (s : ℕ) :
    ((1 - C a * X : ℝ[X]) ^ s).natDegree = s := by
  have hdeg : (1 : ℝ[X]).degree < (C a * X).degree := by
    simpa using (Polynomial.degree_C_lt_degree_C_mul_X (b := (1 : ℝ)) ha)
  have hd : (1 - C a * X : ℝ[X]).degree = (1 : WithBot ℕ) := by
    rw [degree_sub_eq_right_of_degree_lt hdeg, degree_C_mul_X ha]
  have hn : (1 - C a * X : ℝ[X]).natDegree = 1 := by
    exact natDegree_eq_of_degree_eq_some hd
  have hl : (1 - C a * X : ℝ[X]).leadingCoeff ^ s ≠ 0 := by
    rw [leadingCoeff_sub_of_degree_lt' hdeg, leadingCoeff_mul_X, leadingCoeff_C]
    exact pow_ne_zero _ (neg_ne_zero.mpr ha)
  rw [natDegree_pow' hl, hn, mul_one]

/-- The actual candidate rational function has the required explicit nonzero value at infinity. -/
theorem upperNumerator_tendsto_atTop (a : ℝ) (ha : a ≠ 0) (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun x : ℝ => (upperNumerator a r).eval x / (1 - a * x) ^ (r + 1))
      atTop (𝓝 (-(a ^ (r + 1))⁻¹)) := by
  let D : ℝ[X] := (1 - C a * X) ^ (r + 1)
  have hN0 : upperNumerator a r ≠ 0 := by
    intro h
    have hd := upperNumerator_degree a r hr
    simp [h] at hd
  have hD0 : D ≠ 0 := by
    intro h
    have hd := upperDenominator_natDegree a ha (r + 1)
    change D.natDegree = r + 1 at hd
    simp [h] at hd
  have hdeg : (upperNumerator a r).degree = D.degree := by
    rw [degree_eq_natDegree hN0, degree_eq_natDegree hD0, upperNumerator_degree a r hr,
      upperDenominator_natDegree a ha (r + 1)]
  have ht := (upperNumerator a r).div_tendsto_atTop_leadingCoeff_div_of_degree_eq D hdeg
  have hc : (upperNumerator a r).leadingCoeff / D.leadingCoeff = -(a ^ (r + 1))⁻¹ := by
    rw [upperNumerator_leadingCoeff a r hr, upperDenominator_leadingCoeff a ha (r + 1),
      show -a = (-1 : ℝ) * a by ring, mul_pow, pow_succ (-1 : ℝ)]
    field_simp
  rw [hc] at ht
  simpa only [D, eval_pow, eval_sub, eval_one, eval_mul, eval_C, eval_X] using ht

theorem upperNumerator_tailConstant (a : ℝ) (ha : a ≠ 0) (r : ℕ) (hr : 1 ≤ r) :
    numeratorTailConstant a r (upperNumerator a r) = -(a ^ (r + 1))⁻¹ := by
  exact tendsto_nhds_unique
    (numerator_tendsto_atTop a ha r (upperNumerator a r) (upperNumerator_degree a r hr).le)
    (upperNumerator_tendsto_atTop a ha r hr)

def upperPolynomial (a : ℝ) (r : ℕ) : ℝ[X] :=
  rationalTailPolynomial r (numeratorTailResidues a r (upperNumerator a r))

def upperCoefficient (a : ℝ) (r n : ℕ) : ℝ :=
  rationalTailCoeff a r (numeratorTailConstant a r (upperNumerator a r))
    (numeratorTailResidues a r (upperNumerator a r)) n

theorem upperPolynomial_degree (a : ℝ) (r : ℕ) : (upperPolynomial a r).natDegree ≤ r :=
  rationalTailPolynomial_degree _ _

/-- The exact continuation at zero; the infinity term contributes positively. -/
theorem upperPolynomial_eval_zero (a : ℝ) (ha : a ≠ 0) (r : ℕ) (hr : 1 ≤ r) :
    (upperPolynomial a r).eval 0 = a ^ (r - 1) + (a ^ (r + 1))⁻¹ := by
  rw [upperPolynomial, numeratorTailPolynomial_eval_zero a ha r (upperNumerator a r)
    (upperNumerator_degree a r hr).le, upperNumerator_eval_zero,
    upperNumerator_tailConstant a ha r hr, sub_neg_eq_add]

theorem upperPolynomial_eval_zero_pos (a : ℝ) (ha : 0 < a) (r : ℕ) (hr : 1 ≤ r) :
    0 < (upperPolynomial a r).eval 0 := by
  rw [upperPolynomial_eval_zero a ha.ne' r hr]
  positivity

theorem upperCoefficient_positive (a : ℝ) (r n : ℕ) :
    upperCoefficient a r (n + 1) = a ^ (n + 1) * (upperPolynomial a r).eval ((n : ℝ) + 1) :=
  rationalTailCoeff_positive _ _ _ _ _

theorem upperCandidate_rational_identity (a : ℝ) (r : ℕ) (hr : 1 ≤ r) (z : ℂ) :
    (upperNumerator a r).eval₂ Complex.ofRealHom z / (1 - (a : ℂ) * z) ^ (r + 1) =
      ((1 - z ^ 2) / (1 - (a : ℂ) * z) ^ 2) * blaschke a z ^ (r - 1) := by
  have he : r + 1 = 2 + (r - 1) := by omega
  simp only [upperNumerator, eval₂_mul, eval₂_sub, eval₂_one, eval₂_pow, eval₂_X, eval₂_C]
  change (1 - z ^ 2) * ((a : ℂ) - z) ^ (r - 1) / _ = _
  rw [he, pow_add, blaschke, div_pow, div_mul_div_comm]

theorem upperCoefficient_hasSum (a : ℝ) (ha : a ≠ 0) (r : ℕ) (hr : 1 ≤ r)
    (z : ℂ) (hz : ‖(a : ℂ) * z‖ < 1) :
    HasSum (fun n : ℕ => (upperCoefficient a r n : ℂ) * z ^ n)
      (((1 - z ^ 2) / (1 - (a : ℂ) * z) ^ 2) * blaschke a z ^ (r - 1)) := by
  rw [← upperCandidate_rational_identity a r hr z]
  exact numerator_hasSum a ha r (upperNumerator a r) (upperNumerator_degree a r hr).le z hz

/-- The normalized candidate belongs to the original polynomial feasible family. -/
def upperNormalizedPolynomial (a : ℝ) (r : ℕ) : ℝ[X] :=
  ((upperPolynomial a r).eval 0)⁻¹ • upperPolynomial a r

theorem upperNormalizedPolynomial_admissible (a : ℝ) (ha : 0 < a) (r : ℕ) (hr : 1 ≤ r) :
    LocalCertification.Extremal.admissible r (upperNormalizedPolynomial a r) := by
  constructor
  · exact (Polynomial.natDegree_smul_le _ _).trans (upperPolynomial_degree a r)
  · rw [upperNormalizedPolynomial, Polynomial.eval_smul, smul_eq_mul]
    exact inv_mul_cancel₀ (upperPolynomial_eval_zero_pos a ha r hr).ne'

end LocalCertification.Asymptotic
