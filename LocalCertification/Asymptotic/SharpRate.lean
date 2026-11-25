import LocalCertification.Asymptotic.SharpUpper
import LocalCertification.Asymptotic.InfiniteDual

open scoped Topology
open Filter Real

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
namespace LocalCertification.Asymptotic

def lowerRateConstant (q : ℝ) : ℝ :=
  2 / (q * (1 + blaschkeCoefficientConstant q * Real.sqrt (3 / 2)))

def upperRateConstant (q : ℝ) : ℝ := 2 * Real.sqrt 2 * upperOscillationConstant q⁻¹ / q

theorem lowerRateConstant_pos (q : ℝ) (hq : 1 < q) : 0 < lowerRateConstant q := by
  have hq0 : 0 < q := by linarith
  have hD := blaschkeCoefficientConstant_pos q hq
  unfold lowerRateConstant
  positivity

theorem upperRateConstant_pos (q : ℝ) (hq : 1 < q) : 0 < upperRateConstant q := by
  have hq0 : 0 < q := by linarith
  have hK := upperOscillationConstant_pos q⁻¹ (inv_pos.mpr hq0) ((inv_lt_one₀ hq0).mpr hq)
  unfold upperRateConstant
  positivity

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

/-- The upper sharp-order estimate with its explicit constant. -/
theorem gamma_rate_upper (q : ℝ) (hq : 1 < q) (r : ℕ) (hr : 2 ≤ r) :
    LocalCertification.Extremal.gamma q r ≤ upperRateConstant q * (q⁻¹) ^ r / Real.sqrt r := by
  have hq0 : 0 < q := by linarith
  have ha : 0 < q⁻¹ := inv_pos.mpr hq0
  have hK := upperOscillationConstant_pos q⁻¹ ha ((inv_lt_one₀ hq0).mpr hq)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 (by linarith)
  have hsm : 0 < Real.sqrt ((r : ℝ) - 1) := Real.sqrt_pos.2 (by linarith)
  have hroot : Real.sqrt r ≤ Real.sqrt 2 * Real.sqrt ((r : ℝ) - 1) := by
    calc
      _ ≤ Real.sqrt (2 * ((r : ℝ) - 1)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := Real.sqrt_mul (by norm_num) _
  calc
    _ ≤ 2 * upperOscillationConstant q⁻¹ /
        (Real.sqrt ((r : ℝ) - 1) * (q ^ (r + 1) + (q⁻¹) ^ (r - 1))) := gamma_sharp_upper q hq r hr
    _ ≤ 2 * upperOscillationConstant q⁻¹ / (Real.sqrt ((r : ℝ) - 1) * q ^ (r + 1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg ha.le _)) hsm.le
    _ = (2 * upperOscillationConstant q⁻¹ * (q⁻¹) ^ (r + 1)) / Real.sqrt ((r : ℝ) - 1) := by
      rw [inv_pow]
      field_simp
    _ ≤ (2 * upperOscillationConstant q⁻¹ * (q⁻¹) ^ (r + 1) * Real.sqrt 2) / Real.sqrt r := by
      apply (div_le_div_iff₀ hsm hs).mpr
      nlinarith [mul_le_mul_of_nonneg_left hroot
        (show 0 ≤ 2 * upperOscillationConstant q⁻¹ * (q⁻¹) ^ (r + 1) by positivity)]
    _ = _ := by unfold upperRateConstant; rw [pow_succ]; field_simp

/-- The matching sharp order holds for every real q>1 and every degree r>=2. -/
theorem gamma_sharp_rate (q : ℝ) (hq : 1 < q) (r : ℕ) (hr : 2 ≤ r) :
    lowerRateConstant q * (q⁻¹) ^ r / Real.sqrt r ≤ LocalCertification.Extremal.gamma q r ∧
      LocalCertification.Extremal.gamma q r ≤ upperRateConstant q * (q⁻¹) ^ r / Real.sqrt r :=
  ⟨gamma_rate_lower q hq r hr, gamma_rate_upper q hq r hr⟩

end LocalCertification.Asymptotic
