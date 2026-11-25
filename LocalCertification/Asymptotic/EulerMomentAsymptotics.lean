import LocalCertification.Asymptotic.EulerMomentDual
import LocalCertification.Asymptotic.SharpTheorem
open scoped Topology
open Filter Set Real Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace LocalCertification.Asymptotic.EulerMoments

/-- The lower sharp-order estimate with its explicit constant. -/
theorem gamma_rate_lower (q : ℝ) (hq : 1 < q) (r : ℕ) (hr : 2 ≤ r) :
    lowerRateConstant q * (q⁻¹) ^ r / Real.sqrt r ≤ LocalCertification.Extremal.gamma q r := by
  have hq0 : 0 < q := by linarith
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 (by linarith)
  have hD := blaschkeCoefficientConstant_pos q hq
  have h1s : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr (by linarith)
  have hroot : Real.sqrt ((r : ℝ) + 1) ≤ Real.sqrt (3 / 2) * Real.sqrt r := by
    calc
      _ ≤ Real.sqrt ((3 / 2) * (r : ℝ)) := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := Real.sqrt_mul (by norm_num) _
  have hden : 1 + blaschkeCoefficientConstant q * Real.sqrt ((r : ℝ) + 1) ≤
      (1 + blaschkeCoefficientConstant q * Real.sqrt (3 / 2)) * Real.sqrt r := by
    nlinarith [mul_le_mul_of_nonneg_left hroot hD.le]
  calc
    _ = 2 * (q⁻¹) ^ (r + 1) /
        ((1 + blaschkeCoefficientConstant q * Real.sqrt (3 / 2)) * Real.sqrt r) := by
      unfold lowerRateConstant
      rw [pow_succ]
      field_simp
    _ ≤ 2 * (q⁻¹) ^ (r + 1) / (1 + blaschkeCoefficientConstant q * Real.sqrt ((r : ℝ) + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ _ := gamma_blaschke_lower q hq r

/-- The matching sharp order holds for every real q>1 and every degree r>=2. -/
theorem gamma_sharp_rate (q : ℝ) (hq : 1 < q) (r : ℕ) (hr : 2 ≤ r) :
    lowerRateConstant q * (q⁻¹) ^ r / Real.sqrt r ≤ LocalCertification.Extremal.gamma q r ∧
      LocalCertification.Extremal.gamma q r ≤ upperRateConstant q * (q⁻¹) ^ r / Real.sqrt r :=
  ⟨gamma_rate_lower q hq r hr, gamma_rate_upper q hq r hr⟩

theorem gamma_log_bounds (q : ℝ) (hq : 1 < q) (r : ℕ) (hr : 2 ≤ r) :
    Real.log (lowerRateConstant q) - (r : ℝ) * Real.log q - Real.log r / 2 ≤ Real.log (LocalCertification.Extremal.gamma q r) ∧
    Real.log (LocalCertification.Extremal.gamma q r) ≤ Real.log (upperRateConstant q) - (r : ℝ) * Real.log q - Real.log r / 2 := by
  have hq0 : 0 < q := by linarith
  have hl := lowerRateConstant_pos q hq
  have hu := upperRateConstant_pos q hq
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hg := LocalCertification.Extremal.gamma_pos q hq r
  have hlp : 0 < lowerRateConstant q * (q⁻¹) ^ r / Real.sqrt r := by positivity
  have hup : 0 < upperRateConstant q * (q⁻¹) ^ r / Real.sqrt r := by positivity
  constructor
  · have h := (Real.log_le_log_iff hlp hg).2 (gamma_rate_lower q hq r hr)
    simpa only [log_sharp_comparison q _ hq0 hl r hr0] using h
  · have h := (Real.log_le_log_iff hg hup).2 (gamma_rate_upper q hq r hr)
    simpa only [log_sharp_comparison q _ hq0 hu r hr0] using h

/-- Taking logarithms retains the strict lower bracket at the actual critical index. -/
theorem criticalDegree_log_bracket (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g)
    (hk : 3 ≤ criticalDegree q g) :
    logarithmicGap q g + Real.log (lowerRateConstant q) / Real.log q <
        degreeLogModel q (criticalDegree q g) ∧
    degreeLogModel q ((criticalDegree q g - 1 : ℕ) : ℝ) ≤
      logarithmicGap q g + Real.log (upperRateConstant q) / Real.log q := by
  let k := criticalDegree q g
  have hlog := Real.log_pos hq
  have hbr := criticalDegree_bracket q hq g hg (by omega)
  have hlo := (gamma_log_bounds q hq k (by omega)).1
  have hup := (gamma_log_bounds q hq (k - 1) (by omega)).2
  have hlstrict := Real.log_lt_log (LocalCertification.Extremal.gamma_pos q hq k) hbr.1
  have hupper := (Real.log_le_log_iff hg (LocalCertification.Extremal.gamma_pos q hq (k - 1))).2 hbr.2
  constructor
  · have hh : Real.log (lowerRateConstant q) - Real.log g <
        (k : ℝ) * Real.log q + Real.log k / 2 := by linarith
    have hh' := (div_lt_div_iff_of_pos_right hlog).2 hh
    convert hh' using 1 <;> dsimp [logarithmicGap, degreeLogModel, k]
    · rw [Real.log_inv]; ring
    · field_simp
  · have hh : ((k - 1 : ℕ) : ℝ) * Real.log q + Real.log ((k - 1 : ℕ) : ℝ) / 2 ≤
        Real.log (upperRateConstant q) - Real.log g := by linarith
    have hh' := (div_le_div_iff_of_pos_right hlog).2 hh
    convert hh' using 1 <;> dsimp [logarithmicGap, degreeLogModel, k]
    · field_simp
    · rw [Real.log_inv]; ring

theorem degreeLogModel_step_bound (q : ℝ) (hq : 1 < q) (k : ℕ) (hk : 2 ≤ k) :
    degreeLogModel q k - degreeLogModel q ((k - 1 : ℕ) : ℝ) ≤
      1 + Real.log 2 / (2 * Real.log q) := by
  have hlog := Real.log_pos hq
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkm : 0 < (k : ℝ) - 1 := by linarith
  have hlogdiff : Real.log (k : ℝ) - Real.log ((k : ℝ) - 1) ≤ Real.log 2 := by
    rw [← Real.log_div hk0.ne' hkm.ne']
    apply (Real.log_le_log_iff (div_pos hk0 hkm) (by norm_num : (0 : ℝ) < 2)).2
    apply (div_le_iff₀ hkm).2
    linarith
  have he : degreeLogModel q k - degreeLogModel q ((k - 1 : ℕ) : ℝ) =
      1 + (Real.log (k : ℝ) - Real.log ((k : ℝ) - 1)) / (2 * Real.log q) := by
    unfold degreeLogModel
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  rw [he]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hlogdiff (by positivity))

/-- An explicit bounded error for the implicit inverse relation, valid once k>=3. -/
theorem criticalDegree_implicit_bound (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g)
    (hk : 3 ≤ criticalDegree q g) :
    |degreeLogModel q (criticalDegree q g) - logarithmicGap q g| ≤ inversionBound q := by
  have hb := criticalDegree_log_bracket q hq g hg hk
  have hs := degreeLogModel_step_bound q hq (criticalDegree q g) (by omega)
  have hlog := Real.log_pos hq
  have hz : 0 ≤ Real.log 2 / (2 * Real.log q) := by positivity
  unfold inversionBound
  rw [abs_le]
  constructor
  · have h := neg_abs_le (Real.log (lowerRateConstant q) / Real.log q)
    linarith [abs_nonneg (Real.log (upperRateConstant q) / Real.log q), hb.1]
  · have h := le_abs_self (Real.log (upperRateConstant q) / Real.log q)
    linarith [abs_nonneg (Real.log (lowerRateConstant q) / Real.log q), hb.2]

theorem criticalDegree_implicit_eventually (q : ℝ) (hq : 1 < q) :
    ∀ᶠ g : ℝ in 𝓝[>] (0 : ℝ),
      |degreeLogModel q (criticalDegree q g) - logarithmicGap q g| ≤ inversionBound q := by
  filter_upwards [self_mem_nhdsWithin,
    (criticalDegree_tendsto_atTop q hq).eventually (eventually_ge_atTop 3)] with g hg hk
  exact criticalDegree_implicit_bound q hq g hg hk

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

/-- The sharp-order statement in the paper's real-power notation. -/
theorem sharp_order (q : ℝ) (hq : 1 < q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      c * q ^ (-(r : ℝ)) / Real.sqrt r ≤ LocalCertification.Extremal.gamma q r ∧
      LocalCertification.Extremal.gamma q r ≤ C * q ^ (-(r : ℝ)) / Real.sqrt r := by
  refine ⟨lowerRateConstant q, upperRateConstant q, lowerRateConstant_pos q hq,
    upperRateConstant_pos q hq, ?_⟩
  intro r hr
  simpa only [LocalCertification.Extremal.inverse_pow_eq_real_decay] using gamma_sharp_rate q hq r hr

theorem logarithmicGap_eq_logb (q g : ℝ) : logarithmicGap q g = Real.logb q g⁻¹ := rfl

/-- The exact original minimum obeys L-(1/2)log_q L+O_q(1), L=log_q(1/g). -/
theorem criticalDegree_logb_inversion (q : ℝ) (hq : 1 < q) :
    (fun g : ℝ => (criticalDegree q g : ℝ) -
      (Real.logb q g⁻¹ - (1 / 2) * Real.logb q (Real.logb q g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
  convert criticalDegree_logarithmic_inversion q hq using 1
  funext g
  unfold logarithmicGap Real.logb
  ring

/-- Sharp critical-sequence order and logarithmic inversion for every fixed real q>1. -/
theorem sharp_order_and_inversion (q : ℝ) (hq : 1 < q) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      c * q ^ (-(r : ℝ)) / Real.sqrt r ≤ LocalCertification.Extremal.gamma q r ∧
      LocalCertification.Extremal.gamma q r ≤ C * q ^ (-(r : ℝ)) / Real.sqrt r) ∧
    ((fun g : ℝ => (criticalDegree q g : ℝ) -
      (Real.logb q g⁻¹ - (1 / 2) * Real.logb q (Real.logb q g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ))) :=
  ⟨sharp_order q hq, criticalDegree_logb_inversion q hq⟩


end LocalCertification.Asymptotic.EulerMoments
