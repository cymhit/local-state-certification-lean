import LocalCertification.Extremal.GeometricSeriesDerivatives

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter Polynomial
noncomputable section
namespace LocalCertification.Extremal.GeometricSeries

/-- The exact geometric generating function bounds every nonnegative weighted binomial. -/
theorem weighted_choose_le_geometric (q : ℝ) (hq : 1 < q) (r k : ℕ) :
    (q⁻¹)^(k+1)*(k.choose r : ℝ) ≤ ((q-1)⁻¹)^(r+1) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have ht : 0 < q⁻¹ := inv_pos.mpr hq0
  have ht1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).mpr hq
  have hs := hasSum_choose_mul_geometric_via_derivatives r (q⁻¹) ht ht1
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

end LocalCertification.Extremal.GeometricSeries
