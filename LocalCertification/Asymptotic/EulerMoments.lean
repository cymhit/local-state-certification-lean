import LocalCertification.Asymptotic.BlaschkeCauchyBound
import Mathlib.Analysis.Analytic.Order
import Mathlib.Combinatorics.Enumerative.Stirling

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Topology
open Filter Metric Set
noncomputable section
namespace LocalCertification.Asymptotic.EulerMoments

/-- Finite ordinary-derivative form of the higher Euler operator. -/
def eulerExpansion (k : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), (Nat.stirlingSecond k j : ℂ) * z^j * iteratedDeriv j f z

theorem blaschke_deriv_root_zero (a : ℝ) (ha : |a| < 1) (s j : ℕ) (hj : j < s) :
    iteratedDeriv j (fun z => blaschke a z ^ s) (a : ℂ) = 0 := by
  have haa : ‖(a : ℂ) * (a : ℂ)‖ < 1 := by
    rw [← pow_two, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact (sq_lt_one_iff_abs_lt_one a).mpr ha
  have hf : AnalyticAt ℂ (blaschke a) (a : ℂ) := by
    unfold blaschke
    exact (analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (blaschke_denominator_ne_zero a a haa)
  have hzero : blaschke a (a : ℂ) = 0 := by simp [blaschke]
  have hone : (1 : ℕ∞) ≤ analyticOrderAt (blaschke a) (a : ℂ) := by
    exact Order.one_le_iff_ne_zero.mpr (hf.analyticOrderAt_ne_zero.mpr hzero)
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.pow s)).mp _ j hj
  rw [analyticOrderAt_pow hf]
  simpa using nsmul_le_nsmul_right hone s

theorem eulerExpansion_root_zero (a : ℝ) (ha : |a| < 1) (s k : ℕ) (hk : k < s) :
    eulerExpansion k (fun z => blaschke a z ^ s) (a : ℂ) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [blaschke_deriv_root_zero a ha s j (by have := Finset.mem_range.mp hj; omega)]
  ring

theorem eulerExpansion_monomial (k n : ℕ) (c z : ℂ) :
    eulerExpansion k (fun w => c * w^n) z = (n : ℂ)^k * c * z^n := by
  unfold eulerExpansion
  have hp : (n : ℂ)^k = ∑ j ∈ Finset.range (k+1),
      (Nat.stirlingSecond k j : ℂ) * (n.descFactorial j : ℂ) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n k
  rw [hp, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  by_cases hjn : j ≤ n
  · have hpow : z^j * z^(n-j) = z^n := by rw [← pow_add, Nat.add_sub_of_le hjn]
    calc
      _ = (Nat.stirlingSecond k j : ℂ) * (n.descFactorial j : ℂ) * c * (z^j * z^(n-j)) := by ring
      _ = _ := by rw [hpow]
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < j)]

theorem blaschke_eulerExpansion_hasSum (a : ℝ) (ha : |a| < 1) (s k : ℕ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => (n : ℂ)^k * (blaschkeCoeff a s n : ℂ) * z^n)
      (eulerExpansion k (fun w => blaschke a w^s) z) := by
  have hterm (j : ℕ) : HasSum
      (fun n => (Nat.stirlingSecond k j : ℂ) * z^j *
        iteratedDeriv j (blaschkeSeriesTerm a s n) z)
      ((Nat.stirlingSecond k j : ℂ) * z^j *
        iteratedDeriv j (fun w => blaschke a w^s) z) := by
    have hs := (blaschke_cauchy_uniform_derivatives a ha s j).hasSum
      (show z ∈ closedBall 0 1 by simpa using hz)
    exact hs.mul_left _
  have hs := hasSum_sum (s := Finset.range (k+1)) (fun j _ => hterm j)
  convert hs using 1
  · funext n
    exact (eulerExpansion_monomial k n (blaschkeCoeff a s n : ℂ) z).symm
  · rfl

theorem eulerExpansion_succ (k : ℕ) (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) :
    eulerExpansion (k+1) f z = z * deriv (eulerExpansion k f) z := by
  have hfder (j : ℕ) : AnalyticAt ℂ (iteratedDeriv j f) z := by
    induction j with
    | zero => simpa using hf
    | succ j ih => simpa [iteratedDeriv_succ] using ih.deriv
  have hd (j : ℕ) : HasDerivAt
      (fun w => (Nat.stirlingSecond k j : ℂ) * w^j * iteratedDeriv j f w)
      ((Nat.stirlingSecond k j : ℂ) *
        ((j : ℂ) * z^(j-1) * iteratedDeriv j f z + z^j * iteratedDeriv (j+1) f z)) z := by
    convert (((hasDerivAt_pow j z).mul (hfder j).differentiableAt.hasDerivAt).const_mul
      (Nat.stirlingSecond k j : ℂ)) using 1 <;> simp [iteratedDeriv_succ, mul_assoc]
  have hdall := (HasDerivAt.fun_sum (u := Finset.range (k+1)) (fun j _ => hd j)).deriv
  change deriv (eulerExpansion k f) z = _ at hdall
  rw [hdall, Finset.mul_sum]
  have hterm (j : ℕ) : z * ((Nat.stirlingSecond k j : ℂ) *
      ((j : ℂ) * z^(j-1) * iteratedDeriv j f z + z^j * iteratedDeriv (j+1) f z)) =
      (Nat.stirlingSecond k j : ℂ) * (j : ℂ) * z^j * iteratedDeriv j f z +
      (Nat.stirlingSecond k j : ℂ) * z^(j+1) * iteratedDeriv (j+1) f z := by
    cases j with
    | zero => simp; ring
    | succ j => simp [pow_succ]; ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  let F := fun j => (Nat.stirlingSecond k j : ℂ) * (j : ℂ) * z^j * iteratedDeriv j f z
  have hshift : (∑ j ∈ Finset.range (k+1), F (j+1)) = ∑ j ∈ Finset.range (k+1), F j := by
    have h := Finset.sum_range_succ' F (k+1)
    rw [Finset.sum_range_succ] at h
    simpa [F, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self k)] using h.symm
  unfold eulerExpansion
  rw [Finset.sum_range_succ']
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, add_zero]
  simp only [Nat.stirlingSecond, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    _ = ∑ j ∈ Finset.range (k+1), F (j+1) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [F, Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := hshift

/-- Iteration of the actual differential operator `z D`. -/
def euler : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f => f
  | k+1, f => fun z => z * deriv (euler k f) z

/-- The iterated Euler operator is a finite combination of ordinary derivatives. -/
theorem eulerExpansion_eq_euler (k : ℕ) (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) : eulerExpansion k f z = euler k f z := by
  induction k generalizing z with
  | zero => simp [eulerExpansion, euler]
  | succ k ih =>
    have heq : eulerExpansion k f =ᶠ[𝓝 z] euler k f := by
      filter_upwards [hf.eventually_analyticAt] with w hw
      exact ih w hw
    rw [eulerExpansion_succ k f z hf, heq.deriv_eq]
    rfl

theorem euler_root_zero (a : ℝ) (ha : |a| < 1) (s k : ℕ) (hk : k < s) :
    euler k (fun z => blaschke a z^s) (a : ℂ) = 0 := by
  have haa : ‖(a : ℂ) * (a : ℂ)‖ < 1 := by
    rw [← pow_two, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact (sq_lt_one_iff_abs_lt_one a).mpr ha
  have hf : AnalyticAt ℂ (fun z => blaschke a z^s) (a : ℂ) := by
    unfold blaschke
    exact ((analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (blaschke_denominator_ne_zero a a haa)).pow s
  rw [← eulerExpansion_eq_euler k _ _ hf]
  exact eulerExpansion_root_zero a ha s k hk

theorem blaschke_euler_hasSum (a : ℝ) (ha : |a| < 1) (s k : ℕ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => (n : ℂ)^k * (blaschkeCoeff a s n : ℂ) * z^n)
      (euler k (fun w => blaschke a w^s) z) := by
  have haz : ‖(a : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hz (abs_nonneg a)).trans_lt (by simpa using ha)
  have hf : AnalyticAt ℂ (fun w => blaschke a w^s) z := by
    unfold blaschke
    exact ((analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (blaschke_denominator_ne_zero a z haz)).pow s
  rw [← eulerExpansion_eq_euler k _ _ hf]
  exact blaschke_eulerExpansion_hasSum a ha s k z hz

theorem blaschkeCoeff_hasSum_root_moment (a : ℝ) (ha : |a| < 1)
    (s k : ℕ) (hk : k < s) :
    HasSum (fun n : ℕ => (n : ℝ)^k * blaschkeCoeff a s n * a^n) 0 := by
  have hs := blaschke_euler_hasSum a ha s k (a : ℂ) (by simpa using ha.le)
  rw [euler_root_zero a ha s k hk] at hs
  have hr := Complex.reCLM.hasSum hs
  simpa [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul] using hr

end LocalCertification.Asymptotic.EulerMoments
