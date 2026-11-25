import LocalCertification.Asymptotic.InversionBounds

open scoped Topology
open Filter Set Real Asymptotics

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
namespace LocalCertification.Asymptotic

theorem logarithmicGap_pos (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g) (hg1 : g < 1) :
    0 < logarithmicGap q g :=
  div_pos (Real.log_pos ((one_lt_inv₀ hg).mpr hg1)) (Real.log_pos hq)

/-- The bounded implicit error is negligible relative to the actual critical degree. -/
theorem criticalDegree_implicit_div_tendsto_zero (q : ℝ) (hq : 1 < q) :
    Tendsto (fun g : ℝ =>
      (degreeLogModel q (criticalDegree q g) - logarithmicGap q g) / (criticalDegree q g : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hk : Tendsto (fun g : ℝ => (criticalDegree q g : ℝ)) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (criticalDegree_tendsto_atTop q hq)
  have hi := tendsto_inv_atTop_zero.comp hk
  have hb : Tendsto (fun g : ℝ => inversionBound q / (criticalDegree q g : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using (tendsto_const_nhds (x := inversionBound q)).mul hi
  apply squeeze_zero_norm' _ hb
  filter_upwards [criticalDegree_implicit_eventually q hq,
    (criticalDegree_tendsto_atTop q hq).eventually (eventually_ge_atTop 1)] with g hbound hpos
  have hkpos : (0 : ℝ) < criticalDegree q g := by exact_mod_cast (show 0 < criticalDegree q g by omega)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hkpos]
  exact div_le_div_of_nonneg_right hbound hkpos.le

/-- L/k tends to one, derived from the actual strict-threshold index. -/
theorem logarithmicGap_div_criticalDegree_tendsto_one (q : ℝ) (hq : 1 < q) :
    Tendsto (fun g : ℝ => logarithmicGap q g / (criticalDegree q g : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hk : Tendsto (fun g : ℝ => (criticalDegree q g : ℝ)) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (criticalDegree_tendsto_atTop q hq)
  have hl : Tendsto (fun g : ℝ => Real.log (criticalDegree q g : ℝ) / (criticalDegree q g : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hk
  have hmodel : Tendsto (fun g : ℝ => degreeLogModel q (criticalDegree q g) / (criticalDegree q g : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hh : Tendsto (fun g : ℝ => (1 : ℝ) + (1 / (2 * Real.log q)) *
        (Real.log (criticalDegree q g : ℝ) / (criticalDegree q g : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := 1 / (2 * Real.log q))).mul hl)
    apply hh.congr'
    filter_upwards [(criticalDegree_tendsto_atTop q hq).eventually (eventually_ge_atTop 1)] with g hg
    have hk0 : (criticalDegree q g : ℝ) ≠ 0 := by exact_mod_cast (show criticalDegree q g ≠ 0 by omega)
    unfold degreeLogModel
    field_simp
  have hh := hmodel.sub (criticalDegree_implicit_div_tendsto_zero q hq)
  convert hh using 1
  · funext g; ring
  · norm_num

/-- Replacing log k by log L incurs a vanishing error. -/
theorem log_gap_sub_log_degree_tendsto_zero (q : ℝ) (hq : 1 < q) :
    Tendsto (fun g : ℝ => Real.log (logarithmicGap q g) - Real.log (criticalDegree q g : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (logarithmicGap_div_criticalDegree_tendsto_one q hq)
  simp only [Real.log_one] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    (criticalDegree_tendsto_atTop q hq).eventually (eventually_ge_atTop 1)] with g hg hg1 hk
  have hL := logarithmicGap_pos q hq g hg hg1
  have hk0 : (criticalDegree q g : ℝ) ≠ 0 := by exact_mod_cast (show criticalDegree q g ≠ 0 by omega)
  exact Real.log_div hL.ne' hk0

/-- An explicit eventual bounded error for the paper's logarithmic inversion. -/
theorem criticalDegree_explicit_eventually (q : ℝ) (hq : 1 < q) :
    ∀ᶠ g : ℝ in 𝓝[>] (0 : ℝ),
      |(criticalDegree q g : ℝ) -
        (logarithmicGap q g - Real.log (logarithmicGap q g) / (2 * Real.log q))| ≤ inversionBound q + 1 := by
  have he : Tendsto (fun g : ℝ =>
      (Real.log (logarithmicGap q g) - Real.log (criticalDegree q g : ℝ)) / (2 * Real.log q))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (log_gap_sub_log_degree_tendsto_zero q hq).div_const (2 * Real.log q)
  have heabs : Tendsto (fun g : ℝ =>
      |(Real.log (logarithmicGap q g) - Real.log (criticalDegree q g : ℝ)) / (2 * Real.log q)|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa only [Real.norm_eq_abs, abs_zero] using he.norm
  filter_upwards [criticalDegree_implicit_eventually q hq,
    (tendsto_order.mp heabs).2 1 (by norm_num)] with g hbound he1
  have hid : (criticalDegree q g : ℝ) -
      (logarithmicGap q g - Real.log (logarithmicGap q g) / (2 * Real.log q)) =
      (degreeLogModel q (criticalDegree q g) - logarithmicGap q g) +
      (Real.log (logarithmicGap q g) - Real.log (criticalDegree q g : ℝ)) / (2 * Real.log q) := by
    unfold degreeLogModel
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hbound he1.le)

/-- Logarithmic inversion with fixed-q constants and the strict threshold convention. -/
theorem criticalDegree_logarithmic_inversion (q : ℝ) (hq : 1 < q) :
    (fun g : ℝ => (criticalDegree q g : ℝ) -
      (logarithmicGap q g - Real.log (logarithmicGap q g) / (2 * Real.log q)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (inversionBound q + 1)
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using criticalDegree_explicit_eventually q hq

end LocalCertification.Asymptotic
