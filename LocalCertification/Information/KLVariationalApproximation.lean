import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Bounded logarithmic tests for relative entropy

The logarithmic density is clipped to a bounded interval, with the correct
negative endpoint at density zero. Its nonnegative Fenchel expression converges
to `klFun` even at zero. These pointwise facts support a Fatou argument for the
converse variational entropy bound on arbitrary measurable spaces.
-/

set_option autoImplicit false
open Filter
open scoped Topology

namespace LocalCertification.Information

/-- A bounded logarithmic test; the zero-density value tends to minus infinity. -/
noncomputable def clippedLog (n : ℕ) (r : ℝ) : ℝ :=
  if r = 0 then -(n : ℝ) else max (-(n : ℝ)) (min (n : ℝ) (Real.log r))

theorem abs_clippedLog_le (n : ℕ) (r : ℝ) : |clippedLog n r| ≤ (n : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hr : r = 0
  · simp [clippedLog, hr, abs_of_nonneg hn]
  · rw [clippedLog, ite_eq_right hr, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clipping toward zero leaves the exponential Fenchel expression nonnegative. -/
theorem clippedLog_entropy_nonneg (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ r * clippedLog n r - Real.exp (clippedLog n r) + 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hz : r = 0
  · simp only [clippedLog, hz, ↓reduceIte, zero_mul, zero_sub]
    have hexp : Real.exp (-(n : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hn)
    linarith
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  have hneg : -(n : ℝ) ≤ (n : ℝ) := by linarith
  by_cases hlo : Real.log r ≤ -(n : ℝ)
  · have ht : clippedLog n r = -(n : ℝ) := by
      simp [clippedLog, hz, min_eq_right (hlo.trans hneg), max_eq_left hlo]
    rw [ht]
    have hre : r ≤ Real.exp (-(n : ℝ)) := by
      simpa [Real.exp_log hrp] using Real.exp_le_exp.mpr hlo
    have hprod : 0 ≤ (r - Real.exp (-(n : ℝ))) * (-(n : ℝ)) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hre) (neg_nonpos.mpr hn)
    have hk := InformationTheory.klFun_nonneg (Real.exp_pos (-(n : ℝ))).le
    simp only [InformationTheory.klFun, Real.log_exp] at hk
    nlinarith
  by_cases hhi : (n : ℝ) ≤ Real.log r
  · have ht : clippedLog n r = (n : ℝ) := by
      simp [clippedLog, hz, min_eq_left hhi]
    rw [ht]
    have hre : Real.exp (n : ℝ) ≤ r := by
      simpa [Real.exp_log hrp] using Real.exp_le_exp.mpr hhi
    have hprod : 0 ≤ (r - Real.exp (n : ℝ)) * (n : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hre) hn
    have hk := InformationTheory.klFun_nonneg (Real.exp_pos (n : ℝ)).le
    simp only [InformationTheory.klFun, Real.log_exp] at hk
    nlinarith
  · have ht : clippedLog n r = Real.log r := by
      simp [clippedLog, hz, min_eq_right (le_of_not_ge hhi),
        max_eq_right (le_of_not_ge hlo)]
    rw [ht, Real.exp_log hrp]
    have hk := InformationTheory.klFun_nonneg hr
    unfold InformationTheory.klFun at hk
    linarith

/-- For a positive density, bounded logarithmic tests eventually equal its logarithm. -/
theorem clippedLog_eventually_eq_log (r : ℝ) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, clippedLog n r = Real.log r := by
  obtain ⟨N, hN⟩ := exists_nat_ge |Real.log r|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbound : |Real.log r| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  have hb := abs_le.mp hbound
  simp [clippedLog, hr.ne', min_eq_right hb.2, max_eq_right hb.1]

/-- The Fenchel expressions approach the entropy integrand, including density zero. -/
theorem clippedLog_entropy_tendsto (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => r * clippedLog n r - Real.exp (clippedLog n r) + 1)
      atTop (nhds (InformationTheory.klFun r)) := by
  by_cases hz : r = 0
  · subst r
    have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    have he := Real.tendsto_exp_atBot.comp hn
    have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (nhds 0)).sub he).add_const (1 : ℝ)
    simpa [clippedLog, InformationTheory.klFun] using ht
  · have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    apply tendsto_const_nhds.congr'
    filter_upwards [clippedLog_eventually_eq_log r hp] with n hn
    simp only [hn, InformationTheory.klFun, Real.exp_log hp]
    ring

end LocalCertification.Information
