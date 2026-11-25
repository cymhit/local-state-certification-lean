import LocalCertification.Asymptotic.WienerExtremum
import LocalCertification.Asymptotic.EulerMomentDual

/-! # The classical square-root upper bound for repeated-node interpolation

Dilating the Blaschke power gives a feasible series with a geometric
coefficient weight. Parseval and Cauchy–Schwarz control its positive-order
norm uniformly in the interpolation node.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
open Polynomial
open scoped BigOperators
noncomputable section
namespace LocalCertification.Asymptotic.Wiener

private theorem dilation_norm_bound (b R : ℝ) (hb : |b| < 1) (hR : 1 < R) (s : ℕ) :
    let t := fun n : ℕ => blaschkeCoeff b s (n + 1) * R⁻¹ ^ (n + 1)
    Summable (fun n => |t n|) ∧
      (∑' n, |t n|) ≤ Real.sqrt (1 / (R ^ 2 - 1)) := by
  let t := fun n : ℕ => blaschkeCoeff b s (n + 1) * R⁻¹ ^ (n + 1)
  let w := fun n : ℕ => (R ^ (n+1)) ^ 2
  have hR0 : 0 < R := by linarith
  have hw (n : ℕ) : 0 < w n := by dsimp [w]; positivity
  have hc := (hasSum_nat_add_iff' (f := fun n => blaschkeCoeff b s n ^ 2) 1).mpr
    (blaschkeCoeff_hasSum_sq b hb s)
  simp only [Finset.range_one, Finset.sum_singleton, blaschkeCoeff_zero_index] at hc
  have hE : HasSum (fun n : ℕ => w n * t n ^ 2) (1 - (b ^ s)^2) := by
    apply hc.congr_fun
    intro n
    simp only [t, w, inv_pow]
    field_simp
  have htheta0 : 0 ≤ (R ^ 2)⁻¹ := by positivity
  have htheta : (R ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hg := (hasSum_geometric_of_lt_one htheta0 htheta).mul_left ((R ^ 2)⁻¹)
  have hInv : HasSum (fun n => (w n)⁻¹) (1 / (R^2 - 1)) := by
    convert hg using 1
    · funext n
      simp only [w, ← pow_mul, inv_pow, ← mul_inv, Nat.mul_comm]
      congr 2
      ring
    · field_simp
  have habs : Summable (fun n => |t n|) := by
    have h := (summable_nat_add_iff 1).mpr (blaschkeCoeff_summable_abs b hb s)
    apply h.of_nonneg_of_le (fun _ => abs_nonneg _)
    intro n
    dsimp only [t]
    rw [abs_mul, abs_of_nonneg (pow_nonneg (inv_pos.mpr hR0).le _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (inv_pos.mpr hR0).le
      (inv_lt_one_of_one_lt₀ hR).le)
  refine ⟨habs, ?_⟩
  have hh := tsum_abs_le_weighted_sqrt t w (1 - (b ^ s)^2) hw hE hInv.summable
  rw [hInv.tsum_eq] at hh
  apply hh.trans
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg (b^s)]))

/-- The positive-order coefficient cost is at most √(e s), with s=r+1. -/
theorem schaffer_upper (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (r : ℕ) :
    phi a r ≤ Real.sqrt (Real.exp 1 * (r + 1 : ℕ)) := by
  let s := r + 1
  let R := Real.sqrt (1 + (s : ℝ)⁻¹)
  have hs : 0 < (s : ℝ) := by dsimp [s]; positivity
  have hR : 1 < R := by
    have h := Real.sq_sqrt (show 0 ≤ 1 + (s : ℝ)⁻¹ by positivity)
    dsimp only [R]
    nlinarith [Real.sqrt_nonneg (1 + (s : ℝ)⁻¹), inv_pos.mpr hs]
  have hR0 : 0 < R := by linarith
  have hR2 : R ^ 2 = 1 + (s : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  let b := a / R
  have hb : 0 < b := div_pos ha hR0
  have hb1 : |b| < 1 := by rw [abs_of_pos hb]; exact (div_lt_one hR0).mpr (ha1.trans hR)
  let f := fun n : ℕ => R^s * (blaschkeCoeff b s (n+1) * R⁻¹ ^ (n+1))
  obtain ⟨hsum, ht⟩ := dilation_norm_bound b R hb1 hR s
  have hRs : 0 < R^s := pow_pos hR0 s
  have habs : HasSum (fun n => |f n|) (R^s * ∑' n, |blaschkeCoeff b s (n+1) * R⁻¹ ^ (n+1)|) := by
    simpa only [f, abs_mul, abs_of_pos hRs] using hsum.hasSum.mul_left (R^s)
  have hf : MomentFeasible a r f := by
    refine ⟨habs.summable, ?_⟩
    intro p hp
    have h := (EulerMoments.blaschkeCoeff_hasSum_positive_polynomial b hb1 s p (by dsimp [s]; omega)).mul_left (R^s)
    convert h using 1
    · funext n
      dsimp only [f, b]
      rw [div_pow, inv_pow]
      ring
    · dsimp only [b, s]
      rw [div_pow]
      field_simp
  have hq : 1 < a⁻¹ := (one_lt_inv₀ ha).mpr ha1
  have eq := phi_eq_real_moment_infimum a⁻¹ hq r
  simp only [inv_inv] at eq
  rw [eq]
  have hbdd : BddBelow (tailNorm '' {f | MomentFeasible a r f}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨g, _, rfl⟩
    exact tsum_nonneg (fun _ => abs_nonneg _)
  have hcost : momentInfimum a r ≤ tailNorm f := csInf_le hbdd ⟨f, hf, rfl⟩
  have htail : tailNorm f ≤ R^s * Real.sqrt s := by
    rw [tailNorm, habs.tsum_eq]
    apply mul_le_mul_of_nonneg_left _ hRs.le
    simpa only [hR2, add_sub_cancel_left, one_div, inv_inv] using ht
  have hexp : (R ^ s)^2 ≤ Real.exp 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hR2]
    calc
      _ ≤ (Real.exp ((s : ℝ)⁻¹)) ^ s :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((s : ℝ)⁻¹)]) _
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hroot : R^s ≤ Real.sqrt (Real.exp 1) :=
    (Real.le_sqrt (by positivity) (Real.exp_pos _).le).mpr hexp
  apply (hcost.trans htail).trans
  rw [Real.sqrt_mul (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)

end LocalCertification.Asymptotic.Wiener
