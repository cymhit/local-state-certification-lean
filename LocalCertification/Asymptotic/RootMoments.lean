import LocalCertification.Asymptotic.CoefficientL1
import Mathlib.Algebra.Polynomial.Eval.Degree

open scoped BigOperators Topology
open Finset Finset.Nat

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

theorem blaschkeCoeff_one (a : ℝ) (n : ℕ) :
    blaschkeCoeff a 1 n = blaschkeBaseCoeff a n := by
  rw [blaschkeCoeff]
  rw [Finset.sum_eq_single (0, n)]
  · simp [blaschkeCoeff]
  · rintro ⟨i, j⟩ hij hne
    have hi : i ≠ 0 := by
      intro hi
      subst i
      have hj : j = n := by simpa using mem_antidiagonal.mp hij
      subst j
      exact hne rfl
    simp [blaschkeCoeff, hi]
  · intro h
    exact (h (by simp)).elim

/-- Every polynomial weight is absolutely summable strictly inside the unit disk. -/
theorem blaschkeCoeff_summable_moment_norm (a : ℝ) (ha : |a| < 1)
    (s k : ℕ) (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => ‖(n : ℝ) ^ k * blaschkeCoeff a s n * x ^ n‖) := by
  let M := ∑' n, |blaschkeCoeff a s n|
  have hc := blaschkeCoeff_summable_abs a ha s
  have hb (n : ℕ) : |blaschkeCoeff a s n| ≤ M :=
    hc.le_tsum n (fun _ _ => abs_nonneg _)
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ k * |x| ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hx)
  apply (hg.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_mul, norm_mul, norm_pow, Real.norm_natCast, Real.norm_eq_abs,
    norm_pow, Real.norm_eq_abs]
  calc
    (n : ℝ) ^ k * |blaschkeCoeff a s n| * |x| ^ n ≤ (n : ℝ) ^ k * M * |x| ^ n := by
      gcongr
      exact hb n
    _ = M * ((n : ℝ) ^ k * |x| ^ n) := by ring

theorem blaschkeBaseCoeff_summable_moment_norm (a : ℝ) (ha : |a| < 1)
    (k : ℕ) (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => ‖(n : ℝ) ^ k * blaschkeBaseCoeff a n * x ^ n‖) := by
  simpa only [blaschkeCoeff_one] using blaschkeCoeff_summable_moment_norm a ha 1 k x hx

/-- The zeroth moment of the actual single factor vanishes at its actual real zero. -/
theorem blaschkeBaseCoeff_hasSum_root (a : ℝ) (ha : |a| < 1) :
    HasSum (fun n : ℕ => blaschkeBaseCoeff a n * a ^ n) 0 := by
  have haa : ‖(a : ℂ) * (a : ℂ)‖ < 1 := by
    rw [← pow_two, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact (sq_lt_one_iff_abs_lt_one a).mpr ha
  have hs := Complex.reCLM.hasSum (blaschkeBaseCoeff_hasSum a (a : ℂ) haa)
  simpa [blaschke, ← Complex.ofReal_pow] using hs

private theorem cauchy_hasSum_real {f g : ℕ → ℝ} {F G : ℝ}
    (hf : Summable (fun n => ‖f n‖)) (hg : Summable (fun n => ‖g n‖))
    (hF : HasSum f F) (hG : HasSum g G) :
    HasSum (fun n => ∑ ij ∈ antidiagonal n, f ij.1 * g ij.2) (F * G) := by
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  rw [hF.tsum_eq, hG.tsum_eq] at he
  rw [he]
  exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum

/-- The finite coefficient identity underlying all higher vanishing moments. -/
theorem blaschkeCoeff_moment_succ (a : ℝ) (s k n : ℕ) :
    (n : ℝ) ^ k * blaschkeCoeff a (s + 1) n * a ^ n =
      ∑ l ∈ range (k + 1), (k.choose l : ℝ) *
        ∑ ij ∈ antidiagonal n,
          ((ij.1 : ℝ) ^ l * blaschkeCoeff a s ij.1 * a ^ ij.1) *
          ((ij.2 : ℝ) ^ (k - l) * blaschkeBaseCoeff a ij.2 * a ^ ij.2) := by
  rw [blaschkeCoeff]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  rw [← he, Nat.cast_add, pow_add, add_pow]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- All moments below the number of actual zero factors vanish.
The proof uses absolutely convergent Cauchy products and the finite binomial identity. -/
theorem blaschkeCoeff_hasSum_root_moment (a : ℝ) (ha : |a| < 1)
    (s k : ℕ) (hk : k < s) :
    HasSum (fun n : ℕ => (n : ℝ) ^ k * blaschkeCoeff a s n * a ^ n) 0 := by
  induction s generalizing k with
  | zero => omega
  | succ s ih =>
    have hterm (l : ℕ) (hl : l ∈ range (k + 1)) :
        HasSum (fun n : ℕ => (k.choose l : ℝ) *
          ∑ ij ∈ antidiagonal n,
            ((ij.1 : ℝ) ^ l * blaschkeCoeff a s ij.1 * a ^ ij.1) *
            ((ij.2 : ℝ) ^ (k - l) * blaschkeBaseCoeff a ij.2 * a ^ ij.2)) 0 := by
      have hf := blaschkeCoeff_summable_moment_norm a ha s l a ha
      have hg := blaschkeBaseCoeff_summable_moment_norm a ha (k - l) a ha
      by_cases hls : l < s
      · simpa only [zero_mul, mul_zero] using
          (cauchy_hasSum_real hf hg (ih l hls) hg.of_norm.hasSum).mul_left (k.choose l : ℝ)
      · have hkl : k - l = 0 := by simp only [mem_range] at hl; omega
        have hg0 : HasSum
            (fun n : ℕ => (n : ℝ) ^ (k - l) * blaschkeBaseCoeff a n * a ^ n) 0 := by
          simpa only [hkl, pow_zero, one_mul] using blaschkeBaseCoeff_hasSum_root a ha
        simpa only [mul_zero] using
          (cauchy_hasSum_real hf hg hf.of_norm.hasSum hg0).mul_left (k.choose l : ℝ)
    have h := hasSum_sum (s := range (k + 1)) hterm
    simpa only [Finset.sum_const_zero, ← blaschkeCoeff_moment_succ] using h

/-- Vanishing moments for every actual polynomial of degree below the number of factors. -/
theorem blaschkeCoeff_hasSum_root_polynomial (a : ℝ) (ha : |a| < 1)
    (s : ℕ) (p : Polynomial ℝ) (hp : p.natDegree < s) :
    HasSum (fun n : ℕ => blaschkeCoeff a s n * a ^ n * p.eval (n : ℝ)) 0 := by
  have hterm (k : ℕ) (hk : k ∈ range s) :
      HasSum (fun n : ℕ => p.coeff k * ((n : ℝ) ^ k * blaschkeCoeff a s n * a ^ n)) 0 := by
    simpa only [mul_zero] using
      (blaschkeCoeff_hasSum_root_moment a ha s k (mem_range.mp hk)).mul_left (p.coeff k)
  have h := hasSum_sum (s := range s) hterm
  simp only [Finset.sum_const_zero] at h
  convert h using 1
  funext n
  rw [Polynomial.eval_eq_sum_range' hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The positive-node polynomial identity, with the zero coefficient explicitly removed. -/
theorem blaschkeCoeff_hasSum_positive_polynomial (a : ℝ) (ha : |a| < 1)
    (s : ℕ) (p : Polynomial ℝ) (hp : p.natDegree < s) :
    HasSum (fun n : ℕ => blaschkeCoeff a s (n + 1) * a ^ (n + 1) * p.eval ((n : ℝ) + 1))
      (-(a ^ s) * p.eval 0) := by
  have h := (hasSum_nat_add_iff'
    (f := fun n : ℕ => blaschkeCoeff a s n * a ^ n * p.eval (n : ℝ)) 1).mpr
      (blaschkeCoeff_hasSum_root_polynomial a ha s p hp)
  simpa only [Finset.range_one, Finset.sum_singleton, blaschkeCoeff_zero_index,
    pow_zero, mul_one, Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_sub, neg_mul] using h

/-- The total coefficient mass is the actual boundary value at `z = 1`. -/
theorem blaschkeCoeff_hasSum_one (a : ℝ) (ha : |a| < 1) (s : ℕ) :
    HasSum (blaschkeCoeff a s) ((-1 : ℝ) ^ s) := by
  have hden : (1 : ℂ) - (a : ℂ) ≠ 0 := by
    have h := blaschke_denominator_ne_zero a 1 (by simpa using ha)
    simpa using h
  have hb : blaschke a 1 = ((-1 : ℝ) : ℂ) := by
    unfold blaschke
    push_cast
    field_simp
    ring
  have h := Complex.reCLM.hasSum (blaschkeCoeff_hasSum a s 1 (by simpa using ha))
  simpa only [hb, ← Complex.ofReal_pow, Complex.reCLM_apply, Complex.ofReal_re,
    one_pow, mul_one] using h

end LocalCertification.Asymptotic
