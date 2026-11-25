import LocalCertification.Asymptotic.InfiniteDual
import LocalCertification.Extremal.BinomialMoments

open scoped BigOperators Topology
open Polynomial Finset

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The polynomial continuation of `choose (w+k) k`. -/
def shiftedBinomialPolynomial (k : ℕ) : ℝ[X] :=
  (LocalCertification.Extremal.binomialPolynomial k).comp (X + C (k : ℝ))

theorem shiftedBinomialPolynomial_degree (k : ℕ) :
    (shiftedBinomialPolynomial k).natDegree ≤ k := by
  unfold shiftedBinomialPolynomial
  have h := Polynomial.natDegree_comp_le
    (p := LocalCertification.Extremal.binomialPolynomial k) (q := X + C (k : ℝ))
  simpa only [natDegree_X_add_C, mul_one] using h.trans
    (by simpa only [natDegree_X_add_C, mul_one] using LocalCertification.Extremal.binomialPolynomial_degree k)

theorem shiftedBinomialPolynomial_eval_nat (k n : ℕ) :
    (shiftedBinomialPolynomial k).eval (n : ℝ) = ((n + k).choose k : ℝ) := by
  rw [shiftedBinomialPolynomial, Polynomial.eval_comp]
  simp only [eval_add, eval_X, eval_C]
  rw [← Nat.cast_add, LocalCertification.Extremal.binomialPolynomial_eval_nat]

@[simp] theorem shiftedBinomialPolynomial_eval_zero (k : ℕ) :
    (shiftedBinomialPolynomial k).eval 0 = 1 := by
  simpa using shiftedBinomialPolynomial_eval_nat k 0

/-- Actual power-series expansion of a positive power of the linear denominator. -/
theorem shiftedBinomialPolynomial_hasSum (a : ℝ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) (k : ℕ) :
    HasSum (fun n : ℕ => (a : ℂ) ^ n *
      (((shiftedBinomialPolynomial k).eval (n : ℝ) : ℝ) : ℂ) * z ^ n)
      (1 / (1 - (a : ℂ) * z) ^ (k + 1)) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one k hz
  convert h using 1
  funext n
  rw [shiftedBinomialPolynomial_eval_nat, mul_pow]
  push_cast
  ring

/-- Continuation polynomial for finite partial fractions; index `i` has pole order `r-i+1`. -/
def rationalTailPolynomial (r : ℕ) (A : Fin (r + 1) → ℝ) : ℝ[X] :=
  ∑ i, A i • shiftedBinomialPolynomial (r - i.val)

theorem rationalTailPolynomial_degree (r : ℕ) (A : Fin (r + 1) → ℝ) :
    (rationalTailPolynomial r A).natDegree ≤ r := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((shiftedBinomialPolynomial_degree _).trans (Nat.sub_le _ _))

@[simp] theorem rationalTailPolynomial_eval_zero (r : ℕ) (A : Fin (r + 1) → ℝ) :
    (rationalTailPolynomial r A).eval 0 = ∑ i, A i := by
  simp only [rationalTailPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    shiftedBinomialPolynomial_eval_zero, smul_eq_mul, mul_one]

/-- The coefficients include the polynomial constant part only at index zero. -/
def rationalTailCoeff (a : ℝ) (r : ℕ) (L : ℝ) (A : Fin (r + 1) → ℝ) (n : ℕ) : ℝ :=
  (if n = 0 then L else 0) + a ^ n * (rationalTailPolynomial r A).eval (n : ℝ)

theorem rationalTailCoeff_positive (a : ℝ) (r : ℕ) (L : ℝ) (A : Fin (r + 1) → ℝ)
    (n : ℕ) : rationalTailCoeff a r L A (n + 1) =
      a ^ (n + 1) * (rationalTailPolynomial r A).eval ((n : ℝ) + 1) := by
  simp [rationalTailCoeff]

theorem rationalTailCoeff_zero_continuation (a : ℝ) (r : ℕ) (L : ℝ)
    (A : Fin (r + 1) → ℝ) :
    (rationalTailPolynomial r A).eval 0 = rationalTailCoeff a r L A 0 - L := by
  simp [rationalTailCoeff]

/-- Actual complex generating function, before constructing the partial fractions from `N`. -/
theorem rationalTailCoeff_hasSum (a : ℝ) (z : ℂ) (hz : ‖(a : ℂ) * z‖ < 1)
    (r : ℕ) (L : ℝ) (A : Fin (r + 1) → ℝ) :
    HasSum (fun n : ℕ => (rationalTailCoeff a r L A n : ℂ) * z ^ n)
      ((L : ℂ) + ∑ i, (A i : ℂ) / (1 - (a : ℂ) * z) ^ (r - i.val + 1)) := by
  have hterm (i : Fin (r + 1)) :
      HasSum (fun n : ℕ => (A i : ℂ) * ((a : ℂ) ^ n *
        (((shiftedBinomialPolynomial (r - i.val)).eval (n : ℝ) : ℝ) : ℂ) * z ^ n))
        ((A i : ℂ) / (1 - (a : ℂ) * z) ^ (r - i.val + 1)) := by
    simpa only [mul_one_div] using (shiftedBinomialPolynomial_hasSum a z hz (r - i.val)).mul_left (A i : ℂ)
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hterm i)
  have hc : HasSum (fun n : ℕ => if n = 0 then (L : ℂ) else 0) (L : ℂ) := hasSum_ite_eq 0 _
  convert hc.add hsum using 1
  funext n
  simp only [rationalTailCoeff, rationalTailPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sum, add_mul, Finset.mul_sum, Finset.sum_mul]
  have hz0 : (↑(if n = 0 then L else 0) : ℂ) * z ^ n = if n = 0 then (L : ℂ) else 0 := by
    by_cases hn : n = 0 <;> simp [hn]
  rw [hz0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end LocalCertification.Asymptotic
