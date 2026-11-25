import LocalCertification.Extremal.Envelope
import Mathlib.Algebra.Polynomial.Eval.SMul
set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Set Filter Polynomial
noncomputable section
namespace LocalCertification.Extremal

theorem polynomialNode_envelope_bounds (q : ℝ) (hq : 1 < q) (p : ℝ[X]) (x : OnePoint ℕ) :
    lowerEnvelope q p ≤ polynomialNode q 0 p x ∧ polynomialNode q 0 p x ≤ upperEnvelope q p := by
  induction x using OnePoint.rec with
  | infty => exact envelope_zero_bounds q hq p
  | coe k =>
    rw [← weightedValue_eq_node]
    exact ⟨lowerEnvelope_le q hq p k, le_upperEnvelope q hq p k⟩

private theorem signed_interval_bound (a t l u : ℝ) (hl : l ≤ t) (hu : t ≤ u) :
    2*a*t ≤ a*(u+l) + |a| *(u-l) := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hu)]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge ha)) (sub_nonneg.mpr hl)]

/-- Every admissible polynomial obeys the dual lower bound. -/
theorem envelopeRatio_lower (q : ℝ) (hq : 1 < q) (r : ℕ) {p : ℝ[X]}
    (hp : admissible r p) : 2 / (1 + extremalValue q r) ≤ envelopeRatio q p := by
  obtain ⟨c, n, x, μ, hc, hmax, hx, hμ, hn, he, htv, hcontact⟩ := finite_extremal_dual q hq r
  have hm := finite_dual_mass q r x μ he
  have hpval := finite_dual_polynomial q r x μ he p hp.1
  rw [hp.2] at hpval
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => signed_interval_bound (μ i)
    (polynomialNode q 0 p (x i)) (lowerEnvelope q p) (upperEnvelope q p)
    (polynomialNode_envelope_bounds q hq p (x i)).1 (polynomialNode_envelope_bounds q hq p (x i)).2)
  have hsum : 2 * (∑ i, μ i * polynomialNode q 0 p (x i)) ≤
      (∑ i, μ i) * (upperEnvelope q p + lowerEnvelope q p) +
        (∑ i, |μ i|) * (upperEnvelope q p - lowerEnvelope q p) := by
    simpa only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, mul_assoc] using hs
  rw [← hpval, hm, htv] at hsum
  have hB : 0 < 1 + extremalValue q r := by have h := one_lt_extremalValue q hq r; linarith
  apply (div_le_div_iff₀ hB (envelope_denominator_pos q hq p)).mpr
  nlinarith

theorem gamma_lower (q : ℝ) (hq : 1 < q) (r : ℕ) :
    2 / (1 + extremalValue q r) ≤ gamma q r := by
  apply le_csInf (envelope_ratios_nonempty q r)
  rintro t ⟨p, hp, rfl⟩
  exact envelopeRatio_lower q hq r hp


/-- The polynomial obtained from an actual maximizer. -/
def extremizerPolynomial (q : ℝ) (r : ℕ) (c : CoeffSpace r) : ℝ[X] :=
  (extremalValue q r - c.1)⁻¹ • coefficientPolynomial c

theorem extremizer_denominator_pos (q : ℝ) (hq : 1 < q) (r : ℕ)
    {c : CoeffSpace r} (hc : c ∈ feasible q r) : 0 < extremalValue q r - c.1 := by
  have hh : |c.1| ≤ 1 := hc ∞
  have hB := one_lt_extremalValue q hq r
  have hu := (abs_le.mp hh).2
  linarith

theorem extremizerPolynomial_admissible (q : ℝ) (hq : 1 < q) (r : ℕ)
    {c : CoeffSpace r} (hc : c ∈ feasible q r) (hmax : extrapolation r c = extremalValue q r) :
    admissible r (extremizerPolynomial q r c) := by
  have hH := extremizer_denominator_pos q hq r hc
  have heval : (coefficientPolynomial c).eval 0 = extremalValue q r - c.1 := by
    rw [extrapolation_formula] at hmax
    linarith
  constructor
  · exact (Polynomial.natDegree_smul_le _ _).trans (coefficientPolynomial_degree c)
  · simp only [extremizerPolynomial, Polynomial.eval_smul, smul_eq_mul, heval]
    exact inv_mul_cancel₀ hH.ne'

theorem extremizerPolynomial_envelope_bounds (q : ℝ) (hq : 1 < q) (r : ℕ)
    {c : CoeffSpace r} (hc : c ∈ feasible q r) :
    (-1-c.1)/(extremalValue q r-c.1) ≤ lowerEnvelope q (extremizerPolynomial q r c) ∧
    upperEnvelope q (extremizerPolynomial q r c) ≤ (1-c.1)/(extremalValue q r-c.1) := by
  have hH := extremizer_denominator_pos q hq r hc
  have hv (k : ℕ) : weightedValue q (extremizerPolynomial q r c) k =
      (polynomialNode q c.1 (coefficientPolynomial c) (k : OnePoint ℕ)-c.1) /
        (extremalValue q r-c.1) := by
    simp only [weightedValue, extremizerPolynomial, Polynomial.eval_smul, smul_eq_mul, polynomialNode_nat]
    ring
  have hl (k : ℕ) : (-1-c.1)/(extremalValue q r-c.1) ≤
      weightedValue q (extremizerPolynomial q r c) k := by
    rw [hv]
    apply (div_le_div_iff_of_pos_right hH).mpr
    have h := (abs_le.mp (hc (k : OnePoint ℕ))).1
    linarith
  have hu (k : ℕ) : weightedValue q (extremizerPolynomial q r c) k ≤
      (1-c.1)/(extremalValue q r-c.1) := by
    rw [hv]
    apply (div_le_div_iff_of_pos_right hH).mpr
    have h := (abs_le.mp (hc (k : OnePoint ℕ))).2
    linarith
  constructor
  · apply le_csInf (Set.range_nonempty _)
    rintro t ⟨k, rfl⟩
    exact hl k
  · apply csSup_le (Set.range_nonempty _)
    rintro t ⟨k, rfl⟩
    exact hu k

private theorem ratio_of_envelope_bounds (B h l u : ℝ) (hB : 1 < B) (hH : 0 < B-h)
    (hl : (-1-h)/(B-h) ≤ l) (hu : u ≤ (1-h)/(B-h)) (hden : 0 < 1-l) :
    (u-l)/(1-l) ≤ 2/(1+B) := by
  let L := (-1-h)/(B-h)
  let U := (1-h)/(B-h)
  have hL : 0 < 1-L := sub_pos.mpr ((div_lt_one hH).mpr (by linarith))
  have hU : U < 1 := (div_lt_one hH).mpr (by linarith)
  have hstep : (U-l)/(1-l) ≤ (U-L)/(1-L) := by
    apply (div_le_div_iff₀ hden hL).mpr
    have hprod := mul_nonneg (le_of_lt (sub_pos.mpr hU)) (sub_nonneg.mpr hl)
    nlinarith
  have hnum : U-L = 2/(B-h) := by dsimp [L, U]; ring
  have hdenL : 1-L = (1+B)/(B-h) := by
    dsimp [L]
    field_simp
    ring
  calc
    _ ≤ (U-l)/(1-l) := div_le_div_of_nonneg_right (sub_le_sub_right hu l) hden.le
    _ ≤ (U-L)/(1-L) := hstep
    _ = 2/(1+B) := by
      rw [hnum, hdenL]
      field_simp

theorem extremizerPolynomial_ratio_le (q : ℝ) (hq : 1 < q) (r : ℕ)
    {c : CoeffSpace r} (hc : c ∈ feasible q r) :
    envelopeRatio q (extremizerPolynomial q r c) ≤ 2/(1+extremalValue q r) := by
  have hb := extremizerPolynomial_envelope_bounds q hq r hc
  exact ratio_of_envelope_bounds _ _ _ _ (one_lt_extremalValue q hq r)
    (extremizer_denominator_pos q hq r hc) hb.1 hb.2 (envelope_denominator_pos q hq _)

theorem gamma_eq_extremalValue (q : ℝ) (hq : 1 < q) (r : ℕ) :
    gamma q r = 2/(1+extremalValue q r) := by
  apply le_antisymm ?_ (gamma_lower q hq r)
  obtain ⟨c, hc, hmax⟩ := extremalValue_attained q hq r
  have hp := extremizerPolynomial_admissible q hq r hc hmax
  exact (csInf_le (envelope_ratios_bddBelow q hq r)
    ⟨extremizerPolynomial q r c, hp, rfl⟩).trans (extremizerPolynomial_ratio_le q hq r hc)

theorem gamma_pos (q : ℝ) (hq : 1 < q) (r : ℕ) : 0 < gamma q r := by
  rw [gamma_eq_extremalValue q hq r]
  apply div_pos (by norm_num)
  have h := one_lt_extremalValue q hq r
  linarith

theorem gamma_attained (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ p : ℝ[X], admissible r p ∧ envelopeRatio q p = gamma q r := by
  obtain ⟨c, hc, hmax⟩ := extremalValue_attained q hq r
  have hp := extremizerPolynomial_admissible q hq r hc hmax
  refine ⟨extremizerPolynomial q r c, hp, ?_⟩
  rw [gamma_eq_extremalValue q hq r]
  exact le_antisymm (extremizerPolynomial_ratio_le q hq r hc) (envelopeRatio_lower q hq r hp)

end LocalCertification.Extremal
