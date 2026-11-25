import LocalCertification.Asymptotic.WienerSharpOrder

/-! # Strict inversion of the repeated-node interpolation estimate -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology
open Filter Set Real Asymptotics
noncomputable section
namespace LocalCertification.Asymptotic.Wiener

private theorem log_inversion_of_model_bound (q : ℝ) (hq : 1 < q) (M : ℝ)
    (hk : Tendsto (criticalDegree q) (𝓝[>] 0) atTop)
    (hmodel : ∀ᶠ g : ℝ in 𝓝[>] 0, |degreeLogModel q (criticalDegree q g) - logarithmicGap q g| ≤ M) :
    (fun g : ℝ => (criticalDegree q g : ℝ) -
      (Real.logb q g⁻¹ - (1/2) * Real.logb q (Real.logb q g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
  let K := fun g => (criticalDegree q g : ℝ)
  have hK : Tendsto K (𝓝[>] (0 : ℝ)) atTop := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hk
  have hKpos : ∀ᶠ g : ℝ in 𝓝[>] 0, 0 < K g := hK.eventually (eventually_gt_atTop 0)
  have hL := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hK
  have hdiv : Tendsto (fun g => (degreeLogModel q (K g) - logarithmicGap q g) / K g)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hM : Tendsto (fun g => M / K g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        (tendsto_const_nhds (x := M)).mul (tendsto_inv_atTop_zero.comp hK)
    apply squeeze_zero_norm' _ hM
    filter_upwards [hmodel, hKpos] with g hb hp
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp]
    exact div_le_div_of_nonneg_right hb hp.le
  have hmodelRatio : Tendsto (fun g => degreeLogModel q (K g) / K g)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hh : Tendsto (fun g => (1 : ℝ) + (1 / (2 * Real.log q)) * (Real.log (K g) / K g))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa only [Function.comp_apply, id_eq, mul_zero, add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := 1/(2*Real.log q))).mul hL)
    apply hh.congr'
    filter_upwards [hKpos] with g hp
    dsimp [degreeLogModel]
    field_simp
  have hratio : Tendsto (fun g => logarithmicGap q g / K g) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    convert hmodelRatio.sub hdiv using 1
    · funext g; ring
    · norm_num
  have hlog : Tendsto (fun g => Real.log (logarithmicGap q g) - Real.log (K g))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    rw [Real.log_one] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds, hKpos] with g hg hg1 hp
    exact Real.log_div (logarithmicGap_pos q hq g hg hg1).ne' hp.ne'
  have hsmall : ∀ᶠ g : ℝ in 𝓝[>] 0,
      |(Real.log (logarithmicGap q g) - Real.log (K g)) / (2 * Real.log q)| < 1 := by
    have h := (hlog.div_const (2*Real.log q)).norm
    simp only [zero_div, Real.norm_eq_abs, abs_zero] at h
    exact (tendsto_order.mp h).2 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound (M + 1)
  filter_upwards [hmodel, hsmall] with g hb hs
  simp only [Real.norm_eq_abs, norm_one, mul_one]
  have hid : K g - (Real.logb q g⁻¹ - (1/2)*Real.logb q (Real.logb q g⁻¹)) =
      (degreeLogModel q (K g) - logarithmicGap q g) +
      (Real.log (logarithmicGap q g) - Real.log (K g))/(2*Real.log q) := by
    dsimp only [Real.logb, degreeLogModel, logarithmicGap]
    ring
  rw [show (criticalDegree q g : ℝ) = K g from rfl, hid]
  exact (abs_add_le _ _).trans (add_le_add hb hs.le)

/-- Strict inversion is derived from the supplied pair of decay bounds. In particular
the existence and minimality of the crossing use this same upper estimate. -/
theorem inversion_of_bounds (q : ℝ) (hq : 1 < q) (l u : ℝ) (hl : 0 < l) (hu : 0 < u)
    (hbound : ∀ r : ℕ, 2 ≤ r → l*q⁻¹^r/Real.sqrt r ≤ Extremal.gamma q r ∧
      Extremal.gamma q r ≤ u*q⁻¹^r/Real.sqrt r) :
    (fun g : ℝ => (criticalDegree q g : ℝ) -
      (Real.logb q g⁻¹ - (1/2)*Real.logb q (Real.logb q g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have hz : Tendsto (fun r : ℕ => u * q⁻¹ ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr hq0).le (inv_lt_one_of_one_lt₀ hq)))
  have spec (g : ℝ) (hg : 0 < g) : Extremal.gamma q (criticalDegree q g) < g := by
    have hgg := (tendsto_order.mp hz).2 g hg
    obtain ⟨n, hn, ht⟩ := ((eventually_ge_atTop (2 : ℕ)).and hgg).exists
    have h1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n by omega))
    have he : Extremal.gamma q n < g := (hbound n hn).2.trans_lt
      ((div_le_self (by positivity) h1).trans_lt ht)
    exact Nat.sInf_mem (show {r : ℕ | Extremal.gamma q r < g}.Nonempty from ⟨n, he⟩)
  have htop : Tendsto (criticalDegree q) (𝓝[>] 0) atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (Extremal.gamma_pos q hq n)).filter_mono
      nhdsWithin_le_nhds] with g hg hgn
    by_contra h
    have hle : criticalDegree q g ≤ n := by omega
    exact (not_lt_of_ge ((Extremal.gamma_strictAnti q hq).antitone hle))
      ((spec g hg).trans hgn)
  let t := Real.log q
  have ht : 0 < t := Real.log_pos hq
  let M := |Real.log l/t| + |Real.log u/t| + 1 + Real.log 2/(2*t)
  apply log_inversion_of_model_bound q hq M htop
  filter_upwards [self_mem_nhdsWithin, htop.eventually (eventually_ge_atTop 3)] with g hg hk
  let k := criticalDegree q g
  have hspec := spec g hg
  have hprev : g ≤ Extremal.gamma q (k-1) := by
    by_contra! h
    have hle : k ≤ k-1 := Nat.sInf_le h
    omega
  have hp (n : ℕ) (h : 2 ≤ n) : 0 < Real.sqrt n :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hlb : Real.log l - (k : ℝ)*t - Real.log k/2 < Real.log g := by
    have h := Real.log_lt_log (div_pos (mul_pos hl (pow_pos (inv_pos.mpr hq0) k)) (hp k (by omega)))
      ((hbound k (by omega)).1.trans_lt hspec)
    simpa only [log_sharp_comparison q l hq0 hl k (by omega)] using h
  have hub : Real.log g ≤ Real.log u - ((k-1 : ℕ):ℝ)*t - Real.log ((k-1:ℕ):ℝ)/2 := by
    have h := Real.log_le_log hg (hprev.trans (hbound (k-1) (by omega)).2)
    simpa only [log_sharp_comparison q u hq0 hu (k-1) (by omega)] using h
  have lo : logarithmicGap q g + Real.log l/t ≤ degreeLogModel q k := by
    apply (le_of_mul_le_mul_right (a := t) _ ht)
    dsimp only [logarithmicGap, degreeLogModel, t] at *
    rw [Real.log_inv]
    field_simp
    linarith
  have hi : degreeLogModel q ((k-1:ℕ):ℝ) ≤ logarithmicGap q g + Real.log u/t := by
    apply (le_of_mul_le_mul_right (a := t) _ ht)
    dsimp only [logarithmicGap, degreeLogModel, t] at *
    rw [Real.log_inv]
    field_simp
    linarith
  have hs := degreeLogModel_step_bound q hq k (by omega)
  have hlog2 : 0 ≤ Real.log 2/(2*t) := by positivity
  change |degreeLogModel q k - logarithmicGap q g| ≤ M
  unfold M
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log l/t), abs_nonneg (Real.log u/t)]
  · dsimp only [t] at *
    linarith [le_abs_self (Real.log u / Real.log q), abs_nonneg (Real.log l / Real.log q)]

end LocalCertification.Asymptotic.Wiener

namespace LocalCertification.Manuscript

/-- Sharp decay and strict logarithmic inversion, both obtained from the
repeated-node Wiener estimates, for every positive real parameter d. -/
theorem wiener_sharp_order_and_inversion (d : ℝ) (hd : 0 < d) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      c * (d + 1)^(-(r : ℝ)) / Real.sqrt r ≤ gamma d r ∧
      gamma d r ≤ C * (d + 1)^(-(r : ℝ)) / Real.sqrt r) ∧
    ((fun g : ℝ => (criticalDegree d g : ℝ) -
      (Real.logb (d+1) g⁻¹ - (1/2) * Real.logb (d+1) (Real.logb (d+1) g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ))) := by
  have hq : 1 < d + 1 := by linarith
  obtain ⟨l, u, hl, hu, hbound⟩ := Asymptotic.Wiener.gamma_sharp_order (d+1) hq
  exact ⟨⟨l, u, hl, hu, by simpa only [Extremal.inverse_pow_eq_real_decay, gamma] using hbound⟩,
    Asymptotic.Wiener.inversion_of_bounds (d+1) hq l u hl hu hbound⟩

/-- Sharp step-point decay and strict inversion in integer local dimension,
proved by repeated-node Wiener interpolation. -/
theorem physical_wiener_sharp_order_and_inversion (d : ℕ) (hd : 2 ≤ d) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ j : ℕ, 2 ≤ j →
      c * ((d : ℝ) + 1) ^ (-(j : ℝ)) / Real.sqrt j ≤ gamma d j ∧
      gamma d j ≤ C * ((d : ℝ) + 1) ^ (-(j : ℝ)) / Real.sqrt j) ∧
    ((fun g : ℝ => (criticalDegree d g : ℝ) -
      (Real.logb ((d : ℝ) + 1) g⁻¹ -
        (1 / 2) * Real.logb ((d : ℝ) + 1) (Real.logb ((d : ℝ) + 1) g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ))) :=
  wiener_sharp_order_and_inversion d (by exact_mod_cast (show 0 < d by omega))

end LocalCertification.Manuscript
