import LocalCertification.Information.TestingLog

set_option autoImplicit false
namespace LocalCertification.Information

/-- The actual binary terminal information decreases with the allowed error on (0,1/2). -/
theorem testingThreshold_antitone {δ ε : ℝ} (hδ : 0<δ) (hδε : δ≤ε) (hε : ε<1/2) :
    testingThreshold ε≤testingThreshold δ := by
  have hε0 : 0<ε := hδ.trans_le hδε
  have hratio : (1-ε)/ε≤(1-δ)/δ := by
    apply (div_le_div_iff₀ hε0 hδ).mpr
    nlinarith
  have hlog := Real.log_le_log (div_pos (by linarith : 0<1-ε) hε0) hratio
  exact mul_le_mul (show 1-2*ε≤1-2*δ by linarith) hlog
    (testing_parameter_pos ε hε0 hε).le (by linarith)

/-- A fixed positive comparison constant for an arbitrary fixed confidence cutoff below one half. -/
noncomputable def confidenceFactor (δstar : ℝ) : ℝ :=
  min (1/6) (testingThreshold δstar/Real.log 3)

theorem confidenceFactor_pos (δstar : ℝ) (h0 : 0<δstar) (hhalf : δstar<1/2) :
    0<confidenceFactor δstar :=
  lt_min (by norm_num) (div_pos (testingThreshold_pos δstar h0 hhalf) (Real.log_pos (by norm_num)))

/-- A single positive factor controls every actual error level up to any fixed delta-star<1/2. -/
theorem testingThreshold_confidence_lower (δstar : ℝ) (h0 : 0<δstar) (hhalf : δstar<1/2)
    (δ : ℝ) (hδ : 0<δ) (hδstar : δ≤δstar) :
    confidenceFactor δstar*Real.log (1/δ)≤testingThreshold δ := by
  have hδhalf : δ<1/2 := hδstar.trans_lt hhalf
  have hlog0 : 0≤Real.log (1/δ) := (Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))).le
  by_cases hthird : δ≤1/3
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hlog0).trans
      (testingThreshold_log_lower δ hδ hthird)
  · have hthird' : 1/3≤δ := (lt_of_not_ge hthird).le
    have hlog : Real.log (1/δ)≤Real.log 3 :=
      Real.log_le_log (by positivity) ((div_le_iff₀ hδ).mpr (by linarith))
    calc
      _≤(testingThreshold δstar/Real.log 3)*Real.log (1/δ) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hlog0
      _≤(testingThreshold δstar/Real.log 3)*Real.log 3 :=
        mul_le_mul_of_nonneg_left hlog (div_pos (testingThreshold_pos δstar h0 hhalf)
          (Real.log_pos (by norm_num))).le
      _=testingThreshold δstar := div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num)))
      _≤testingThreshold δ := testingThreshold_antitone hδ hδstar hhalf

end LocalCertification.Information
