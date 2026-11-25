import LocalCertification.Asymptotic.BlaschkeBoundary

open scoped BigOperators Topology
open Finset Finset.Nat

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The actual Euler derivative of the rational Blaschke factor. -/
def blaschkeBaseEuler (a : ℝ) (z : ℂ) : ℂ :=
  (((a : ℂ) ^ 2 - 1) * z) / (1 - (a : ℂ) * z) ^ 2

/-- The actual Euler derivative of its `s`th power. -/
def blaschkeEuler (a : ℝ) (s : ℕ) (z : ℂ) : ℂ :=
  (s : ℂ) * blaschke a z ^ (s - 1) * blaschkeBaseEuler a z

private theorem baseEuler_term_succ (a : ℝ) (z : ℂ) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * (blaschkeBaseCoeff a (n + 1) : ℂ) * z ^ (n + 1) =
      (((a : ℂ) ^ 2 - 1) * z) * ((n + 1 : ℕ) : ℂ) * ((a : ℂ) * z) ^ n := by
  simp only [blaschkeBaseCoeff, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_one, mul_pow, pow_succ]
  ring

theorem blaschkeBaseEuler_hasSum (a : ℝ) (z : ℂ) (hz : ‖(a : ℂ) * z‖ < 1) :
    HasSum (fun n : ℕ => (n : ℂ) * (blaschkeBaseCoeff a n : ℂ) * z ^ n)
      (blaschkeBaseEuler a z) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hz).mul_left
    (((a : ℂ) ^ 2 - 1) * z)
  simp_rw [baseEuler_term_succ]
  simpa only [Nat.choose_one_right, mul_assoc, Nat.reduceAdd,
    blaschkeBaseEuler, mul_one_div] using hs

theorem blaschkeBaseEuler_summable_norm (a : ℝ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) :
    Summable (fun n : ℕ => ‖(n : ℂ) * (blaschkeBaseCoeff a n : ℂ) * z ^ n‖) := by
  rw [← summable_nat_add_iff 1]
  have hr : ‖‖(a : ℂ) * z‖‖ < 1 := by simpa using hz
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hr).summable.mul_left
    ‖((a : ℂ) ^ 2 - 1) * z‖
  simp_rw [baseEuler_term_succ]
  simpa only [norm_mul, norm_pow, Complex.norm_natCast,
    Nat.choose_one_right, mul_assoc] using hs

private theorem euler_coeff_succ (a : ℝ) (s n : ℕ) (z : ℂ) :
    (n : ℂ) * (blaschkeCoeff a (s + 1) n : ℂ) * z ^ n =
      (∑ ij ∈ antidiagonal n,
        ((ij.1 : ℂ) * (blaschkeCoeff a s ij.1 : ℂ) * z ^ ij.1) *
          ((blaschkeBaseCoeff a ij.2 : ℂ) * z ^ ij.2)) +
      (∑ ij ∈ antidiagonal n,
        ((blaschkeCoeff a s ij.1 : ℂ) * z ^ ij.1) *
          ((ij.2 : ℂ) * (blaschkeBaseCoeff a ij.2 : ℂ) * z ^ ij.2)) := by
  simp only [blaschkeCoeff, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  rw [← he, Nat.cast_add, pow_add]
  ring

private theorem euler_coeff_zero (a : ℝ) (n : ℕ) (z : ℂ) :
    (n : ℂ) * (blaschkeCoeff a 0 n : ℂ) * z ^ n = 0 := by
  by_cases hn : n = 0 <;> simp [blaschkeCoeff, hn]

theorem blaschkeEuler_summable_norm (a : ℝ) (s : ℕ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) :
    Summable (fun n : ℕ => ‖(n : ℂ) * (blaschkeCoeff a s n : ℂ) * z ^ n‖) := by
  induction s with
  | zero => simp only [euler_coeff_zero, norm_zero]; exact summable_zero
  | succ s ih =>
    have h₁ := summable_norm_sum_mul_antidiagonal_of_summable_norm ih
      (blaschkeBaseCoeff_summable_norm a z hz)
    have h₂ := summable_norm_sum_mul_antidiagonal_of_summable_norm
      (blaschkeCoeff_summable_norm a s z hz) (blaschkeBaseEuler_summable_norm a z hz)
    simp_rw [euler_coeff_succ]
    exact (h₁.add h₂).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_add_le _ _)

private theorem cauchy_hasSum {f g : ℕ → ℂ} {F G : ℂ}
    (hf : Summable (fun n => ‖f n‖)) (hg : Summable (fun n => ‖g n‖))
    (hF : HasSum f F) (hG : HasSum g G) :
    HasSum (fun n => ∑ ij ∈ antidiagonal n, f ij.1 * g ij.2) (F * G) := by
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  rw [hF.tsum_eq, hG.tsum_eq] at he
  rw [he]
  exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum

/-- The Euler-weighted coefficients sum to the actual rational Euler derivative. -/
theorem blaschkeEuler_hasSum (a : ℝ) (s : ℕ) (z : ℂ)
    (hz : ‖(a : ℂ) * z‖ < 1) :
    HasSum (fun n : ℕ => (n : ℂ) * (blaschkeCoeff a s n : ℂ) * z ^ n)
      (blaschkeEuler a s z) := by
  induction s with
  | zero => simp only [euler_coeff_zero, blaschkeEuler, Nat.cast_zero, zero_mul]; exact hasSum_zero
  | succ s ih =>
    have h₁ := cauchy_hasSum (blaschkeEuler_summable_norm a s z hz)
      (blaschkeBaseCoeff_summable_norm a z hz) ih (blaschkeBaseCoeff_hasSum a z hz)
    have h₂ := cauchy_hasSum (blaschkeCoeff_summable_norm a s z hz)
      (blaschkeBaseEuler_summable_norm a z hz) (blaschkeCoeff_hasSum a s z hz)
      (blaschkeBaseEuler_hasSum a z hz)
    have he : blaschkeEuler a s z * blaschke a z +
        blaschke a z ^ s * blaschkeBaseEuler a z = blaschkeEuler a (s + 1) z := by
      cases s with
      | zero => simp [blaschkeEuler]
      | succ s => simp only [blaschkeEuler, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring
    simpa only [euler_coeff_succ, he] using h₁.add h₂

end LocalCertification.Asymptotic
