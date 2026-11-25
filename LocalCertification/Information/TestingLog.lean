import LocalCertification.Information.BinarySupport

set_option autoImplicit false
namespace LocalCertification.Information

/-- For 0 < δ ≤ 1/3, the terminal testing factor is at least one sixth of log(1/δ). -/
theorem testingThreshold_log_lower (δ : ℝ) (hδ : 0<δ) (hthird : δ≤1/3) :
    (1/6)*Real.log (1/δ)≤testingThreshold δ := by
  have hδ1 : δ<1 := by linarith
  have hhalf : δ<1/2 := by linarith
  have hsq : δ≤(1-δ)^2 := by nlinarith [sq_nonneg δ]
  have hlogs : Real.log δ≤2*Real.log (1-δ) := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hδ hsq
  have hlogratio : Real.log (1/δ)/2≤Real.log ((1-δ)/δ) := by
    rw [Real.log_div (by linarith : 1-δ≠0) hδ.ne',Real.log_div one_ne_zero hδ.ne',Real.log_one]
    linarith
  have hmul := mul_le_mul_of_nonneg_right (show (1/3:ℝ)≤1-2*δ by linarith)
    (testing_parameter_pos δ hδ hhalf).le
  unfold testingThreshold
  nlinarith

end LocalCertification.Information
