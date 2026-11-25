import LocalCertification.Asymptotic.RationalTail
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators Topology
open Polynomial Finset Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- Express the actual numerator in the variable `t = 1 - a*z`. -/
def affineNumerator (a : ℝ) (N : ℝ[X]) : ℝ[X] := N.comp (C (a⁻¹) * (1 - X))

theorem affineNumerator_degree (a : ℝ) (N : ℝ[X]) :
    (affineNumerator a N).natDegree ≤ N.natDegree := by
  have hlinear : (C (a⁻¹) * (1 - X) : ℝ[X]).natDegree ≤ 1 := by
    apply Polynomial.natDegree_mul_le.trans
    have h := Polynomial.natDegree_sub_le (1 : ℝ[X]) X
    simpa only [natDegree_C, zero_add, natDegree_one, natDegree_X, Nat.zero_max] using h
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul_left N.natDegree hlinear).trans_eq (Nat.mul_one _))

theorem affineNumerator_eval₂_recovery (a : ℝ) (ha : a ≠ 0) (N : ℝ[X]) (z : ℂ) :
    (affineNumerator a N).eval₂ Complex.ofRealHom (1 - (a : ℂ) * z) =
      N.eval₂ Complex.ofRealHom z := by
  rw [affineNumerator, Polynomial.eval₂_comp]
  congr 1
  simp only [eval₂_mul, eval₂_C, eval₂_sub, eval₂_one, eval₂_X]
  change ((a⁻¹ : ℝ) : ℂ) * (1 - (1 - (a : ℂ) * z)) = z
  rw [Complex.ofReal_inv]
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  field_simp [hac]
  ring

def numeratorTailConstant (a : ℝ) (r : ℕ) (N : ℝ[X]) : ℝ :=
  (affineNumerator a N).coeff (r + 1)

def numeratorTailResidues (a : ℝ) (r : ℕ) (N : ℝ[X]) : Fin (r + 1) → ℝ :=
  fun i => (affineNumerator a N).coeff i.val

/-- Constructive partial fractions of every actual bounded-degree numerator. -/
theorem numerator_partialFractions (a : ℝ) (ha : a ≠ 0) (r : ℕ) (N : ℝ[X])
    (hN : N.natDegree ≤ r + 1) (z : ℂ) (hz : 1 - (a : ℂ) * z ≠ 0) :
    N.eval₂ Complex.ofRealHom z / (1 - (a : ℂ) * z) ^ (r + 1) =
      (numeratorTailConstant a r N : ℂ) +
        ∑ i : Fin (r + 1), (numeratorTailResidues a r N i : ℂ) /
          (1 - (a : ℂ) * z) ^ (r - i.val + 1) := by
  let t : ℂ := 1 - (a : ℂ) * z
  have ht : t ≠ 0 := hz
  have hP : (affineNumerator a N).natDegree < r + 1 + 1 :=
    lt_of_le_of_lt ((affineNumerator_degree a N).trans hN) (Nat.lt_succ_self _)
  have he := Polynomial.eval₂_eq_sum_range' Complex.ofRealHom hP t
  rw [Finset.sum_range_succ] at he
  have hr := affineNumerator_eval₂_recovery a ha N z
  have hsum : N.eval₂ Complex.ofRealHom z =
      (∑ i : Fin (r + 1), (numeratorTailResidues a r N i : ℂ) * t ^ i.val) +
        (numeratorTailConstant a r N : ℂ) * t ^ (r + 1) := by
    rw [← hr]
    change (affineNumerator a N).eval₂ Complex.ofRealHom t = _
    rw [he]
    unfold numeratorTailResidues numeratorTailConstant
    congr 1
    exact (Fin.sum_univ_eq_sum_range
      (fun i : ℕ => ((affineNumerator a N).coeff i : ℂ) * t ^ i) (r + 1)).symm
  change N.eval₂ Complex.ofRealHom z / t ^ (r + 1) = _
  rw [hsum, add_div, Finset.sum_div]
  have hc : (numeratorTailConstant a r N : ℂ) * t ^ (r + 1) / t ^ (r + 1) =
      (numeratorTailConstant a r N : ℂ) := by field_simp
  rw [hc, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : i.val + (r - i.val + 1) = r + 1 := by omega
  have hp : t ^ (r + 1) = t ^ i.val * t ^ (r - i.val + 1) := by rw [← pow_add, he]
  change (numeratorTailResidues a r N i : ℂ) * t ^ i.val / t ^ (r + 1) =
    (numeratorTailResidues a r N i : ℂ) / t ^ (r - i.val + 1)
  rw [hp]
  field_simp

/-- The coefficients and polynomial tail are constructed from `N`, not supplied as assumptions. -/
theorem numerator_hasSum (a : ℝ) (ha : a ≠ 0) (r : ℕ) (N : ℝ[X])
    (hN : N.natDegree ≤ r + 1) (z : ℂ) (hz : ‖(a : ℂ) * z‖ < 1) :
    HasSum (fun n : ℕ =>
      (rationalTailCoeff a r (numeratorTailConstant a r N) (numeratorTailResidues a r N) n : ℂ) * z ^ n)
      (N.eval₂ Complex.ofRealHom z / (1 - (a : ℂ) * z) ^ (r + 1)) := by
  rw [numerator_partialFractions a ha r N hN z (blaschke_denominator_ne_zero a z hz)]
  exact rationalTailCoeff_hasSum a z hz r _ _

theorem numerator_partialFractions_real (a : ℝ) (ha : a ≠ 0) (r : ℕ) (N : ℝ[X])
    (hN : N.natDegree ≤ r + 1) (x : ℝ) (hx : 1 - a * x ≠ 0) :
    N.eval x / (1 - a * x) ^ (r + 1) = numeratorTailConstant a r N +
      ∑ i : Fin (r + 1), numeratorTailResidues a r N i / (1 - a * x) ^ (r - i.val + 1) := by
  have hxc : 1 - (a : ℂ) * (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have he := numerator_partialFractions a ha r N hN (x : ℂ) hxc
  have hev : N.eval₂ Complex.ofRealHom (x : ℂ) = ((N.eval x : ℝ) : ℂ) :=
    Polynomial.eval₂_at_apply Complex.ofRealHom x
  rw [hev] at he
  exact_mod_cast he

/-- The tail polynomial's value at zero differs from the series coefficient by the constant part. -/
theorem numeratorTailPolynomial_eval_zero (a : ℝ) (ha : a ≠ 0) (r : ℕ) (N : ℝ[X])
    (hN : N.natDegree ≤ r + 1) :
    (rationalTailPolynomial r (numeratorTailResidues a r N)).eval 0 =
      N.eval 0 - numeratorTailConstant a r N := by
  have h := numerator_partialFractions_real a ha r N hN 0 (by simp)
  simp only [mul_zero, sub_zero, one_pow, div_one] at h
  rw [rationalTailPolynomial_eval_zero]
  linarith

theorem numeratorTailCoeff_zero (a : ℝ) (ha : a ≠ 0) (r : ℕ) (N : ℝ[X])
    (hN : N.natDegree ≤ r + 1) :
    rationalTailCoeff a r (numeratorTailConstant a r N) (numeratorTailResidues a r N) 0 = N.eval 0 := by
  simp only [rationalTailCoeff, ite_true, pow_zero, Nat.cast_zero, one_mul,
    numeratorTailPolynomial_eval_zero a ha r N hN, add_sub_cancel]

/-- The actual real rational function tends to the constructed constant part at infinity. -/
theorem numerator_tendsto_atTop (a : ℝ) (ha : a ≠ 0) (r : ℕ) (N : ℝ[X])
    (hN : N.natDegree ≤ r + 1) :
    Tendsto (fun x : ℝ => N.eval x / (1 - a * x) ^ (r + 1)) atTop
      (𝓝 (numeratorTailConstant a r N)) := by
  have hbase : Tendsto (fun x : ℝ => (1 - a * x)⁻¹) atTop (𝓝 0) := by
    convert tendsto_mul_add_inv_atTop_nhds_zero (-a) 1 (neg_ne_zero.mpr ha) using 1
    funext x
    congr 1
    ring
  have hterm (i : Fin (r + 1)) : Tendsto
      (fun x : ℝ => numeratorTailResidues a r N i / (1 - a * x) ^ (r - i.val + 1))
      atTop (𝓝 0) := by
    simpa only [zero_pow (Nat.succ_ne_zero _), mul_zero, inv_pow, div_eq_mul_inv] using
      (hbase.pow (r - i.val + 1)).const_mul (numeratorTailResidues a r N i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  have htotal : Tendsto
      (fun x : ℝ => numeratorTailConstant a r N +
        ∑ i : Fin (r + 1), numeratorTailResidues a r N i / (1 - a * x) ^ (r - i.val + 1))
      atTop (𝓝 (numeratorTailConstant a r N)) := by
    simpa only [Finset.sum_const_zero, add_zero] using tendsto_const_nhds.add hsum
  apply htotal.congr'
  filter_upwards [eventually_gt_atTop (a⁻¹)] with x hx
  symm
  apply numerator_partialFractions_real a ha r N hN x
  intro hz
  have hxval : x = a⁻¹ := by
    apply mul_left_cancel₀ ha
    rw [mul_inv_cancel₀ ha]
    linarith
  exact (ne_of_gt hx) hxval

/-- Full rational-tail continuation, including the real infinity limit and its correct zero value. -/
theorem rational_tail_exists (a : ℝ) (ha : a ≠ 0) (r : ℕ) (N : ℝ[X])
    (hN : N.natDegree ≤ r + 1) :
    ∃ (f : ℕ → ℝ) (Q : ℝ[X]) (L : ℝ),
      Q.natDegree ≤ r ∧
      (∀ z : ℂ, ‖(a : ℂ) * z‖ < 1 →
        HasSum (fun n => (f n : ℂ) * z ^ n) (N.eval₂ Complex.ofRealHom z / (1 - (a : ℂ) * z) ^ (r + 1))) ∧
      (∀ n : ℕ, f (n + 1) = a ^ (n + 1) * Q.eval ((n : ℝ) + 1)) ∧
      f 0 = N.eval 0 ∧
      Tendsto (fun x : ℝ => N.eval x / (1 - a * x) ^ (r + 1)) atTop (𝓝 L) ∧
      Q.eval 0 = N.eval 0 - L := by
  refine ⟨rationalTailCoeff a r (numeratorTailConstant a r N) (numeratorTailResidues a r N),
    rationalTailPolynomial r (numeratorTailResidues a r N), numeratorTailConstant a r N,
    rationalTailPolynomial_degree _ _, ?_, rationalTailCoeff_positive _ _ _ _,
    numeratorTailCoeff_zero a ha r N hN, numerator_tendsto_atTop a ha r N hN,
    numeratorTailPolynomial_eval_zero a ha r N hN⟩
  exact fun z hz => numerator_hasSum a ha r N hN z hz

end LocalCertification.Asymptotic
