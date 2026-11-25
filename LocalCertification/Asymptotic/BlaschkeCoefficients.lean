import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

open scoped BigOperators Topology
open Finset Finset.Nat

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LocalCertification.Asymptotic

/-- The actual Blaschke factor, with a real zero at `a`. -/
def blaschke (a : ℝ) (z : ℂ) : ℂ := ((a : ℂ) - z) / (1 - (a : ℂ) * z)

/-- The real Taylor coefficients of one Blaschke factor. -/
def blaschkeBaseCoeff (a : ℝ) : ℕ → ℝ
  | 0 => a
  | n + 1 => (a ^ 2 - 1) * a ^ n

/-- Actual coefficients of a Blaschke power, defined by finite Cauchy products. -/
def blaschkeCoeff (a : ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | s + 1, n => ∑ ij ∈ antidiagonal n,
      blaschkeCoeff a s ij.1 * blaschkeBaseCoeff a ij.2

@[simp] theorem blaschkeCoeff_zero_index (a : ℝ) (s : ℕ) :
    blaschkeCoeff a s 0 = a ^ s := by
  induction s with
  | zero => simp [blaschkeCoeff]
  | succ s ih => simp [blaschkeCoeff, blaschkeBaseCoeff, ih, pow_succ]

theorem blaschke_denominator_ne_zero (a : ℝ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) : 1 - (a : ℂ) * z ≠ 0 := by
  intro h
  have h' : (a : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
  simp [h'] at hz

private theorem baseCoeff_mul_pow_succ (a : ℝ) (z : ℂ) (n : ℕ) :
    (blaschkeBaseCoeff a (n + 1) : ℂ) * z ^ (n + 1) =
      (((a : ℂ) ^ 2 - 1) * z) * ((a : ℂ) * z) ^ n := by
  simp only [blaschkeBaseCoeff, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_one, mul_pow, pow_succ]
  ring

theorem blaschkeBaseCoeff_hasSum (a : ℝ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) :
    HasSum (fun n => (blaschkeBaseCoeff a n : ℂ) * z ^ n) (blaschke a z) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, blaschkeBaseCoeff, pow_zero, mul_one]
  have hs := (hasSum_geometric_of_norm_lt_one hz).mul_left (((a : ℂ) ^ 2 - 1) * z)
  convert hs using 1
  · funext n
    exact baseCoeff_mul_pow_succ a z n
  · dsimp [blaschke]
    field_simp [blaschke_denominator_ne_zero a z hz]
    ring

theorem blaschkeBaseCoeff_summable_norm (a : ℝ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) :
    Summable (fun n => ‖(blaschkeBaseCoeff a n : ℂ) * z ^ n‖) := by
  rw [← summable_nat_add_iff 1]
  simp_rw [baseCoeff_mul_pow_succ, norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hz).mul_left _

private theorem coeff_mul_pow_succ (a : ℝ) (s n : ℕ) (z : ℂ) :
    (blaschkeCoeff a (s + 1) n : ℂ) * z ^ n =
      ∑ ij ∈ antidiagonal n,
        ((blaschkeCoeff a s ij.1 : ℂ) * z ^ ij.1) *
          ((blaschkeBaseCoeff a ij.2 : ℂ) * z ^ ij.2) := by
  simp only [blaschkeCoeff, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  rw [← he, pow_add]
  ring

private theorem coeff_mul_pow_zero (a : ℝ) (z : ℂ) (n : ℕ) :
    (blaschkeCoeff a 0 n : ℂ) * z ^ n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0 <;> simp [blaschkeCoeff, hn]

/-- Absolute convergence holds throughout the actual disk `|a z| < 1`. -/
theorem blaschkeCoeff_summable_norm (a : ℝ) (s : ℕ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) :
    Summable (fun n => ‖(blaschkeCoeff a s n : ℂ) * z ^ n‖) := by
  induction s with
  | zero =>
    simp_rw [coeff_mul_pow_zero]
    simpa only [apply_ite, norm_one, norm_zero] using
      (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  | succ s ih =>
    simp_rw [coeff_mul_pow_succ]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => (blaschkeCoeff a s n : ℂ) * z ^ n)
      (g := fun n => (blaschkeBaseCoeff a n : ℂ) * z ^ n)
      ih (blaschkeBaseCoeff_summable_norm a z hz)

/-- The constructed real coefficients sum to the specified rational function power. -/
theorem blaschkeCoeff_hasSum (a : ℝ) (s : ℕ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) :
    HasSum (fun n => (blaschkeCoeff a s n : ℂ) * z ^ n) (blaschke a z ^ s) := by
  induction s with
  | zero =>
    simpa only [coeff_mul_pow_zero, pow_zero] using
      (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
  | succ s ih =>
    have hf := blaschkeCoeff_summable_norm a s z hz
    have hg := blaschkeBaseCoeff_summable_norm a z hz
    have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
    rw [ih.tsum_eq, (blaschkeBaseCoeff_hasSum a z hz).tsum_eq, ← pow_succ] at he
    simpa only [coeff_mul_pow_succ, he] using
      (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum

/-- In particular the coefficient sequence is absolutely summable on the unit circle. -/
theorem blaschkeCoeff_summable_abs (a : ℝ) (ha : |a| < 1) (s : ℕ) :
    Summable (fun n => |blaschkeCoeff a s n|) := by
  simpa using blaschkeCoeff_summable_norm a s 1 (by simpa using ha)

end LocalCertification.Asymptotic
