import LocalCertification.Extremal.BinomialMoments

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- (-1)^r choose(w-1,r), represented polynomially also at extrapolation zero. -/
def decayPolynomial (r : ℕ) : ℝ[X] :=
  (r.factorial : ℝ)⁻¹ • (ascPochhammer ℝ r).comp (C 1-X)

theorem decayPolynomial_admissible (r : ℕ) : admissible r (decayPolynomial r) := by
  constructor
  · apply (Polynomial.natDegree_smul_le _ _).trans
    apply Polynomial.natDegree_comp_le.trans
    have hd : (C (1:ℝ)-X).natDegree ≤ 1 := (Polynomial.natDegree_sub_le _ _).trans (by simp)
    simpa only [ascPochhammer_natDegree, mul_one] using Nat.mul_le_mul_left r hd
  · have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
    simp [decayPolynomial, Polynomial.eval_smul, Polynomial.eval_comp, hf]

theorem decayPolynomial_eval_positive (r k : ℕ) :
    (decayPolynomial r).eval ((k+1 : ℕ) : ℝ) = (-1 : ℝ)^r * (k.choose r : ℝ) := by
  rw [decayPolynomial, Polynomial.eval_smul, Polynomial.eval_comp]
  have he : (C (1:ℝ)-X).eval ((k+1 : ℕ) : ℝ) = -(k:ℝ) := by simp
  rw [he, ascPochhammer_eval_neg_eq_descPochhammer, Nat.cast_choose_eq_descPochhammer_div]
  simp only [smul_eq_mul]
  ring

/-- The alternating sum of the binomial polynomials agrees with the normalized
decay polynomial at every real argument, including the extrapolation point zero. -/
theorem decayPolynomial_eq_alternating_sum (r : ℕ) :
    decayPolynomial r = ∑ k ∈ Finset.range (r + 1), (-1 : ℝ)^k • binomialPolynomial k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective
    ((Nat.cast_injective (R := ℝ)).comp Nat.succ_injective)).mono
  rintro _ ⟨n, rfl⟩
  change (decayPolynomial r).eval ((n + 1 : ℕ) : ℝ) = _
  rw [decayPolynomial_eval_positive]
  simp only [Function.comp_apply, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    binomialPolynomial_eval_nat, smul_eq_mul]
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := r)).symm

/-- The shifted binomial on the right is a polynomial in the real variable;
in particular, its argument at zero is minus one. -/
theorem decayPolynomial_eq_shifted_binomial (r : ℕ) :
    decayPolynomial r = (-1 : ℝ)^r • (binomialPolynomial r).comp (X - 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective
    ((Nat.cast_injective (R := ℝ)).comp Nat.succ_injective)).mono
  rintro _ ⟨n, rfl⟩
  change (decayPolynomial r).eval ((n + 1 : ℕ) : ℝ) = _
  rw [decayPolynomial_eval_positive]
  simp [Polynomial.eval_smul, Polynomial.eval_comp, binomialPolynomial_eval_nat]

theorem decayPolynomial_weighted (q : ℝ) (r k : ℕ) :
    weightedValue q (decayPolynomial r) k = (-1 : ℝ)^r * ((q⁻¹)^(k+1)*(k.choose r : ℝ)) := by
  rw [weightedValue, decayPolynomial_eval_positive]
  ring

/-- The exact geometric generating function bounds every nonnegative weighted binomial. -/
theorem weighted_choose_le_geometric (q : ℝ) (hq : 1 < q) (r k : ℕ) :
    (q⁻¹)^(k+1)*(k.choose r : ℝ) ≤ ((q-1)⁻¹)^(r+1) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have ht : 0 < q⁻¹ := inv_pos.mpr hq0
  have ht1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).mpr hq
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one r (show ‖q⁻¹‖ < 1 by simpa [Real.norm_eq_abs, abs_of_pos hq0] using ht1)
  by_cases hkr : r ≤ k
  · have hi : ((k-r+r).choose r : ℝ) * (q⁻¹)^(k-r) ≤ 1/(1-q⁻¹)^(r+1) := by
      have hle := hs.summable.sum_le_tsum ({k-r} : Finset ℕ)
        (fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.le _))
      simpa only [Finset.sum_singleton, hs.tsum_eq] using hle
    have hm := mul_le_mul_of_nonneg_left hi (pow_nonneg ht.le (r+1))
    have he : (q⁻¹)^(k+1)*(k.choose r : ℝ) =
        (q⁻¹)^(r+1)*(((k-r+r).choose r : ℝ)*(q⁻¹)^(k-r)) := by
      rw [Nat.sub_add_cancel hkr]
      have hk : k+1 = (r+1)+(k-r) := by omega
      rw [hk, pow_add]
      ring
    have hfrac : q⁻¹/(1-q⁻¹) = (q-1)⁻¹ := by
      have hqm : q-1 ≠ 0 := by linarith
      have hden : 1-q⁻¹ ≠ 0 := by linarith
      field_simp
    calc
      _ = _ := he
      _ ≤ _ := hm
      _ = ((q⁻¹)/(1-q⁻¹))^(r+1) := by rw [div_pow]; ring
      _ = _ := by rw [hfrac]
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hkr), Nat.cast_zero, mul_zero]
    positivity

theorem envelopeRatio_le_of_nonnegative_bound (q : ℝ) (hq : 1 < q) (p : ℝ[X]) (C : ℝ)
    (hb : ∀ k, 0 ≤ weightedValue q p k ∧ weightedValue q p k ≤ C) : envelopeRatio q p ≤ C := by
  have hl0 : 0 ≤ lowerEnvelope q p := le_csInf (Set.range_nonempty _) (by rintro t ⟨k, rfl⟩; exact (hb k).1)
  have hl : lowerEnvelope q p = 0 := le_antisymm (envelope_zero_bounds q hq p).1 hl0
  have hu : upperEnvelope q p ≤ C := csSup_le (Set.range_nonempty _) (by rintro t ⟨k, rfl⟩; exact (hb k).2)
  simpa only [envelopeRatio, hl, sub_zero, div_one] using hu

theorem envelopeRatio_le_of_nonpositive_bound (q : ℝ) (hq : 1 < q) (p : ℝ[X]) (C : ℝ)
    (hb : ∀ k, -C ≤ weightedValue q p k ∧ weightedValue q p k ≤ 0) : envelopeRatio q p ≤ C := by
  have hlC : -C ≤ lowerEnvelope q p := le_csInf (Set.range_nonempty _) (by rintro t ⟨k, rfl⟩; exact (hb k).1)
  have hu0 : upperEnvelope q p ≤ 0 := csSup_le (Set.range_nonempty _) (by rintro t ⟨k, rfl⟩; exact (hb k).2)
  have hu : upperEnvelope q p = 0 := le_antisymm hu0 (envelope_zero_bounds q hq p).2
  have hr : envelopeRatio q p ≤ -lowerEnvelope q p := by
    rw [envelopeRatio, hu, zero_sub]
    apply (div_le_iff₀ (envelope_denominator_pos q hq p)).mpr
    nlinarith [sq_nonneg (lowerEnvelope q p)]
  exact hr.trans (by linarith)

theorem gamma_binomial_bound (q : ℝ) (hq : 1 < q) (r : ℕ) :
    gamma q r ≤ ((q-1)⁻¹)^(r+1) := by
  have hg : gamma q r ≤ envelopeRatio q (decayPolynomial r) :=
    csInf_le (envelope_ratios_bddBelow q hq r) ⟨decayPolynomial r, decayPolynomial_admissible r, rfl⟩
  apply hg.trans
  have hn (k : ℕ) : 0 ≤ (q⁻¹)^(k+1)*(k.choose r : ℝ) := by positivity
  rcases neg_one_pow_eq_or ℝ r with hs | hs
  · apply envelopeRatio_le_of_nonnegative_bound q hq
    intro k
    simpa only [decayPolynomial_weighted, hs, one_mul] using
      And.intro (hn k) (weighted_choose_le_geometric q hq r k)
  · apply envelopeRatio_le_of_nonpositive_bound q hq
    intro k
    rw [decayPolynomial_weighted, hs, neg_one_mul]
    exact ⟨neg_le_neg (weighted_choose_le_geometric q hq r k), neg_nonpos.mpr (hn k)⟩

/-- The paper's explicit elementary rate; the proof actually gives its inequality for all q>1. -/
theorem gamma_elementary_decay (q : ℝ) (hq : 2 < q) (r : ℕ) :
    gamma q r ≤ (q-1)^(-((r+1 : ℕ) : ℝ)) := by
  rw [← inverse_pow_eq_real_decay]
  exact gamma_binomial_bound q (by linarith) r

theorem gamma_tendsto_zero_of_two_lt (q : ℝ) (hq : 2 < q) :
    Tendsto (gamma q) atTop (𝓝 0) := by
  have hq1 : 1 < q := by linarith
  have ht0 : 0 ≤ (q-1)⁻¹ := by positivity
  have ht1 : (q-1)⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < q-1)).mpr (by linarith)
  have hgeo : Tendsto (fun r : ℕ => ((q-1)⁻¹)^(r+1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).comp (tendsto_add_atTop_nat 1)
  exact squeeze_zero (gamma_nonneg q hq1) (gamma_binomial_bound q hq1) hgeo

theorem exists_finite_degree_for_gap (q : ℝ) (hq : 2 < q) (g : ℝ) (hg : 0 < g) :
    ∃ r : ℕ, gamma q r < g :=
  ((tendsto_order.mp (gamma_tendsto_zero_of_two_lt q hq)).2 g hg).exists

end LocalCertification.Extremal
