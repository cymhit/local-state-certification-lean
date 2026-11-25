import LocalCertification.Information.BinarySupport
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace LocalCertification.Information

/-- The paper's confidence ratio, in an algebraic form whose value at zero is one. -/
def continuousConfidenceRatio (δ : ℝ) : ℝ :=
  (1 - 2 * δ) * (1 - Real.log (1 - δ) / Real.log δ)

@[simp] theorem continuousConfidenceRatio_zero : continuousConfidenceRatio 0 = 1 := by
  simp [continuousConfidenceRatio]

theorem continuousConfidenceRatio_eq_testing (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1 / 2) :
    continuousConfidenceRatio δ = testingThreshold δ / Real.log (1 / δ) := by
  have hδ1 : δ < 1 := by linarith
  have hl : Real.log δ ≠ 0 := (Real.log_neg hδ hδ1).ne
  rw [continuousConfidenceRatio, testingThreshold, Real.log_div (by linarith) hδ.ne',
    Real.log_div one_ne_zero hδ.ne', Real.log_one]
  field_simp
  ring

/-- The logarithmic divergence at zero gives a vanishing inverse logarithm. -/
theorem inv_log_continuousAt_zero :
    ContinuousAt (fun δ : ℝ => (Real.log δ)⁻¹) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simpa only [Real.log_zero, inv_zero, Function.comp_def] using
    (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero)

theorem continuousConfidenceRatio_continuousAt_zero : ContinuousAt continuousConfidenceRatio 0 := by
  have hlin : ContinuousAt (fun δ : ℝ => 1 - 2 * δ) 0 := by fun_prop
  have hlog : ContinuousAt (fun δ : ℝ => Real.log (1 - δ)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  unfold continuousConfidenceRatio
  simp only [div_eq_mul_inv]
  exact hlin.mul (continuousAt_const.sub (hlog.mul inv_log_continuousAt_zero))

theorem continuousConfidenceRatio_tendsto_zero_right :
    Tendsto continuousConfidenceRatio (𝓝[>] 0) (𝓝 1) := by
  simpa only [continuousConfidenceRatio_zero] using
    continuousConfidenceRatio_continuousAt_zero.continuousWithinAt.tendsto

theorem continuousConfidenceRatio_continuousAt (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1 / 2) :
    ContinuousAt continuousConfidenceRatio δ := by
  have hδ1 : δ < 1 := by linarith
  have hl : Real.log δ ≠ 0 := (Real.log_neg hδ hδ1).ne
  have hlin : ContinuousAt (fun x : ℝ => 1 - 2 * x) δ := by fun_prop
  have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) δ :=
    (continuousAt_const.sub continuousAt_id).log (by change 1 - δ ≠ 0; linarith)
  exact hlin.mul (continuousAt_const.sub (hlog.div (Real.continuousAt_log hδ.ne') hl))

theorem continuousConfidenceRatio_continuousOn (δstar : ℝ) (hhalf : δstar < 1 / 2) :
    ContinuousOn continuousConfidenceRatio (Icc 0 δstar) := by
  intro δ hδ
  by_cases hz : δ = 0
  · subst δ
    exact continuousConfidenceRatio_continuousAt_zero.continuousWithinAt
  · exact (continuousConfidenceRatio_continuousAt δ (lt_of_le_of_ne hδ.1 (Ne.symm hz))
      (hδ.2.trans_lt hhalf)).continuousWithinAt

theorem continuousConfidenceRatio_pos (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ < 1 / 2) :
    0 < continuousConfidenceRatio δ := by
  by_cases hz : δ = 0
  · simp [hz]
  · have hpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
    rw [continuousConfidenceRatio_eq_testing δ hpos hhalf]
    exact div_pos (testingThreshold_pos δ hpos hhalf)
      (Real.log_pos ((lt_div_iff₀ hpos).mpr (by linarith)))

/-- A genuine attained positive minimum of the continuously extended ratio. -/
theorem continuousConfidenceRatio_positive_minimum (δstar : ℝ) (h0 : 0 < δstar)
    (hhalf : δstar < 1 / 2) :
    ∃ δmin ∈ Icc (0 : ℝ) δstar, 0 < continuousConfidenceRatio δmin ∧
      ∀ δ ∈ Icc (0 : ℝ) δstar, continuousConfidenceRatio δmin ≤ continuousConfidenceRatio δ := by
  obtain ⟨δmin, hmem, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr h0.le) (continuousConfidenceRatio_continuousOn δstar hhalf)
  exact ⟨δmin, hmem, continuousConfidenceRatio_pos δmin hmem.1 (hmem.2.trans_lt hhalf), hmin⟩

/-- The full confidence comparison is obtained from compactness, without a one-third split. -/
theorem testingThreshold_confidence_lower_via_continuous_ratio (δstar : ℝ) (h0 : 0 < δstar)
    (hhalf : δstar < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
      c * Real.log (1 / δ) ≤ testingThreshold δ := by
  obtain ⟨δmin, _, hc, hmin⟩ := continuousConfidenceRatio_positive_minimum δstar h0 hhalf
  refine ⟨continuousConfidenceRatio δmin, hc, ?_⟩
  intro δ hδ hcut
  have hl : 0 < Real.log (1 / δ) :=
    Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have h := hmin δ ⟨hδ.le, hcut⟩
  rw [continuousConfidenceRatio_eq_testing δ hδ (hcut.trans_lt hhalf)] at h
  exact (le_div_iff₀ hl).mp h

end LocalCertification.Information
