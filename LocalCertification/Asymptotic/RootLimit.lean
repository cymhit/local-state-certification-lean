import LocalCertification.Asymptotic.CriticalDegree

open scoped Topology
open Filter Real

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
namespace LocalCertification.Asymptotic

theorem log_sharp_comparison (q c : ℝ) (hq : 0 < q) (hc : 0 < c)
    (r : ℕ) (hr : 0 < r) :
    Real.log (c * (q⁻¹) ^ r / Real.sqrt r) =
      Real.log c - (r : ℝ) * Real.log q - Real.log r / 2 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Real.log_div (mul_ne_zero hc.ne' (pow_ne_zero _ (inv_ne_zero hq.ne')))
    (Real.sqrt_pos.2 hrR).ne', Real.log_mul hc.ne' (pow_ne_zero _ (inv_ne_zero hq.ne')),
    Real.log_pow, Real.log_inv, Real.log_sqrt hrR.le]
  ring

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

theorem log_comparison_div_degree_tendsto (q c : ℝ) :
    Tendsto (fun r : ℕ => (Real.log c - (r : ℝ) * Real.log q - Real.log r / 2) / (r : ℝ))
      atTop (𝓝 (-Real.log q)) := by
  have hn : Tendsto (fun r : ℕ => (r : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun r : ℕ => (r : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hl : Tendsto (fun r : ℕ => Real.log (r : ℝ) / (r : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn
  have h := (((tendsto_const_nhds (x := Real.log c)).mul hi).sub (tendsto_const_nhds (x := Real.log q))).sub
    ((tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hl)
  have h' : Tendsto (fun r : ℕ => Real.log c * (r : ℝ)⁻¹ - Real.log q - (1 / 2) * (Real.log (r : ℝ) / (r : ℝ)))
      atTop (𝓝 (-Real.log q)) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  field_simp

/-- The logarithmic exponential rate of the original critical sequence. -/
theorem gamma_log_div_degree_tendsto (q : ℝ) (hq : 1 < q) :
    Tendsto (fun r : ℕ => Real.log (LocalCertification.Extremal.gamma q r) / (r : ℝ)) atTop (𝓝 (-Real.log q)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (log_comparison_div_degree_tendsto q (lowerRateConstant q))
    (log_comparison_div_degree_tendsto q (upperRateConstant q))
  · filter_upwards [eventually_ge_atTop 2] with r hr
    exact div_le_div_of_nonneg_right (gamma_log_bounds q hq r hr).1 (Nat.cast_nonneg r)
  · filter_upwards [eventually_ge_atTop 2] with r hr
    exact div_le_div_of_nonneg_right (gamma_log_bounds q hq r hr).2 (Nat.cast_nonneg r)

/-- The sharp root limit, for every fixed real q>1. -/
theorem gamma_root_limit (q : ℝ) (hq : 1 < q) :
    Tendsto (fun r : ℕ => (LocalCertification.Extremal.gamma q r) ^ (1 / (r : ℝ))) atTop (𝓝 q⁻¹) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp (gamma_log_div_degree_tendsto q hq)
  have he : Real.exp (-Real.log q) = q⁻¹ := by rw [Real.exp_neg, Real.exp_log (by linarith : 0 < q)]
  rw [he] at h
  convert h using 1
  funext r
  rw [Real.rpow_def_of_pos (LocalCertification.Extremal.gamma_pos q hq r)]
  congr 1
  ring

end LocalCertification.Asymptotic
