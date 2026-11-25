import LocalCertification.Asymptotic.EulerMoments
import LocalCertification.Asymptotic.InfiniteDual
open scoped BigOperators Topology OnePoint
open Finset
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace LocalCertification.Asymptotic.EulerMoments

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

theorem blaschkeDual_hasSum_polynomial (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (s : ℕ) (p : Polynomial ℝ) (hp : p.natDegree < s) :
    HasSum (fun n : ℕ => blaschkeDualWeight a s n * a ^ (n + 1) * p.eval ((n : ℝ) + 1))
      (p.eval 0) := by
  have ha : |a| < 1 := by rwa [abs_of_pos ha0]
  have h := (blaschkeCoeff_hasSum_positive_polynomial a ha s p hp).mul_left (-(a ^ s)⁻¹)
  convert h using 1
  · funext n
    unfold blaschkeDualWeight
    ring
  · field_simp

theorem blaschkeDual_hasSum_reproduction (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (s : ℕ) (h : ℝ) (p : Polynomial ℝ) (hp : p.natDegree < s) :
    HasSum (fun n : ℕ => blaschkeDualWeight a s n *
      (h + a ^ (n + 1) * p.eval ((n : ℝ) + 1)))
      (h + p.eval 0 - blaschkeDualInfinity a s * h) := by
  have h₁ := (blaschkeDual_hasSum_mass a ha0 ha1 s).mul_right h
  have h₂ := blaschkeDual_hasSum_polynomial a ha0 ha1 s p hp
  convert h₁.add h₂ using 1
  · funext n; ring
  · ring

theorem blaschkeDual_hasSum_abs (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (s : ℕ) :
    HasSum (fun n => |blaschkeDualWeight a s n|)
      ((a ^ s)⁻¹ * ((∑' n, |blaschkeCoeff a s n|) - a ^ s)) := by
  have ha : |a| < 1 := by rwa [abs_of_pos ha0]
  have hs := (hasSum_nat_add_iff' (f := fun n => |blaschkeCoeff a s n|) 1).mpr
    (blaschkeCoeff_summable_abs a ha s).hasSum
  simp only [Finset.range_one, Finset.sum_singleton, blaschkeCoeff_zero_index,
    abs_of_pos (pow_pos ha0 s)] at hs
  simpa only [blaschkeDualWeight, abs_mul, abs_neg, abs_inv,
    abs_of_pos (pow_pos ha0 s)] using hs.mul_left ((a ^ s)⁻¹)

/-- Total variation of the explicit countably supported dual, with infinity retained. -/
theorem blaschkeDual_totalVariation (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (s : ℕ) :
    (∑' n, |blaschkeDualWeight a s n|) + |blaschkeDualInfinity a s| =
      (a ^ s)⁻¹ * (1 + ∑' n, |blaschkeCoeff a s n|) - 1 := by
  rw [(blaschkeDual_hasSum_abs a ha0 ha1 s).tsum_eq]
  simp only [blaschkeDualInfinity, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_inv, abs_of_pos (pow_pos ha0 s)]
  field_simp
  ring

/-- The real polynomial-node formula is reproduced by the actual infinite dual. -/
theorem blaschkeDual_reproduces_node (q : ℝ) (hq : 1 < q) (r : ℕ)
    (h : ℝ) (p : Polynomial ℝ) (hp : p.natDegree ≤ r) :
    HasSum (fun n : ℕ => blaschkeDualWeight (q⁻¹) (r + 1) n *
      LocalCertification.Extremal.polynomialNode q h p (n : OnePoint ℕ))
      (h + p.eval 0 - blaschkeDualInfinity (q⁻¹) (r + 1) * h) := by
  have hq0 : 0 < q := by linarith
  simpa only [LocalCertification.Extremal.polynomialNode_nat, Nat.cast_add, Nat.cast_one] using
    blaschkeDual_hasSum_reproduction (q⁻¹) (inv_pos.mpr hq0) (inv_lt_one_of_one_lt₀ hq)
      (r + 1) h p (by omega)

private theorem signed_mul_le_abs (x y : ℝ) (hy : |y| ≤ 1) : x * y ≤ |x| := by
  calc
    x * y ≤ |x * y| := le_abs_self _
    _ = |x| * |y| := abs_mul _ _
    _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    _ = |x| := mul_one _

/-- The explicit infinite dual bounds the actual infinite-constraint extremum. -/
theorem extremalValue_le_blaschke_totalVariation (q : ℝ) (hq : 1 < q) (r : ℕ) :
    LocalCertification.Extremal.extremalValue q r ≤
      ((q⁻¹) ^ (r + 1))⁻¹ * (1 + ∑' n, |blaschkeCoeff (q⁻¹) (r + 1) n|) - 1 := by
  have ha0 : 0 < q⁻¹ := inv_pos.mpr (by linarith)
  have ha1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  obtain ⟨c, hc, hmax⟩ := LocalCertification.Extremal.extremalValue_attained q hq r
  have hs := blaschkeDual_reproduces_node q hq r c.1 (LocalCertification.Extremal.coefficientPolynomial c)
    (LocalCertification.Extremal.coefficientPolynomial_degree c)
  have hv : (∑' n : ℕ, blaschkeDualWeight (q⁻¹) (r + 1) n *
      LocalCertification.Extremal.polynomialNode q c.1 (LocalCertification.Extremal.coefficientPolynomial c) (n : OnePoint ℕ)) =
      LocalCertification.Extremal.extremalValue q r - blaschkeDualInfinity (q⁻¹) (r + 1) * c.1 := by
    rw [hs.tsum_eq, ← LocalCertification.Extremal.extrapolation_formula c, hmax]
  have hb := blaschkeDual_hasSum_abs (q⁻¹) ha0 ha1 (r + 1)
  have hle := Summable.tsum_le_tsum
    (fun n : ℕ => signed_mul_le_abs (blaschkeDualWeight (q⁻¹) (r + 1) n)
      (LocalCertification.Extremal.polynomialNode q c.1 (LocalCertification.Extremal.coefficientPolynomial c) (n : OnePoint ℕ))
      (hc (n : OnePoint ℕ))) hs.summable hb.summable
  rw [hv] at hle
  have hInf := signed_mul_le_abs (blaschkeDualInfinity (q⁻¹) (r + 1)) c.1
    (show |c.1| ≤ 1 by simpa using hc ∞)
  have htotal : LocalCertification.Extremal.extremalValue q r ≤
      (∑' n, |blaschkeDualWeight (q⁻¹) (r + 1) n|) + |blaschkeDualInfinity (q⁻¹) (r + 1)| := by
    linarith
  exact htotal.trans_eq (blaschkeDual_totalVariation (q⁻¹) ha0 ha1 (r + 1))

/-- The sharp lower bound first in terms of the actual coefficient norm. -/
theorem gamma_blaschke_coefficient_lower (q : ℝ) (hq : 1 < q) (r : ℕ) :
    2 * (q⁻¹) ^ (r + 1) / (1 + ∑' n, |blaschkeCoeff (q⁻¹) (r + 1) n|) ≤
      LocalCertification.Extremal.gamma q r := by
  have ha0 : 0 < (q⁻¹) ^ (r + 1) := pow_pos (inv_pos.mpr (by linarith)) _
  have hm : 0 ≤ ∑' n, |blaschkeCoeff (q⁻¹) (r + 1) n| := tsum_nonneg (fun _ => abs_nonneg _)
  have hb0 : 0 < 1 + LocalCertification.Extremal.extremalValue q r := by
    have h := LocalCertification.Extremal.one_lt_extremalValue q hq r
    linarith
  have hB := mul_le_mul_of_nonneg_left (extremalValue_le_blaschke_totalVariation q hq r) ha0.le
  simp only [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul] at hB
  rw [LocalCertification.Extremal.gamma_eq_extremalValue q hq r]
  apply (div_le_div_iff₀ (by linarith) hb0).mpr
  nlinarith

/-- The Blaschke lower bound for every real base `q > 1` and every degree. -/
theorem gamma_blaschke_lower (q : ℝ) (hq : 1 < q) (r : ℕ) :
    2 * (q⁻¹) ^ (r + 1) / (1 + blaschkeCoefficientConstant q * Real.sqrt (r + 1)) ≤
      LocalCertification.Extremal.gamma q r := by
  have ha0 : 0 < (q⁻¹) ^ (r + 1) := pow_pos (inv_pos.mpr (by linarith)) _
  have hm : 0 ≤ ∑' n, |blaschkeCoeff (q⁻¹) (r + 1) n| := tsum_nonneg (fun _ => abs_nonneg _)
  have hbound := blaschkeCoeff_tsum_abs_le_q q hq (r + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at hbound
  have hden : 0 < 1 + ∑' n, |blaschkeCoeff (q⁻¹) (r + 1) n| := by linarith
  exact (div_le_div_of_nonneg_left (by positivity) hden (by linarith)).trans
    (gamma_blaschke_coefficient_lower q hq r)


end LocalCertification.Asymptotic.EulerMoments
