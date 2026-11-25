import LocalCertification.Extremal.Gamma
set_option autoImplicit false
open scoped BigOperators Topology OnePoint
noncomputable section
namespace LocalCertification.Extremal

/-- Exact degree-zero interpolation includes the infinity endpoint. -/
theorem degreeZero_extrapolation (q : ℝ) (hq : q ≠ 0) (c : CoeffSpace 0) :
    extrapolation 0 c = q * polynomialNode q c.1 (coefficientPolynomial c) (0 : ℕ) +
      (1-q) * polynomialNode q c.1 (coefficientPolynomial c) ∞ := by
  rw [extrapolation_formula, finite_label_zero, polynomialNode_infty]
  have hp := Polynomial.eq_C_of_natDegree_eq_zero
    (Nat.eq_zero_of_le_zero (coefficientPolynomial_degree c))
  rw [hp]
  simp only [Polynomial.eval_C]
  field_simp
  ring

theorem extremalValue_zero (q : ℝ) (hq : 1 < q) : extremalValue q 0 = 2*q-1 := by
  apply le_antisymm ?_ (extremalValue_lower q hq 0)
  obtain ⟨c, hc, hmax⟩ := extremalValue_attained q hq 0
  have he := degreeZero_extrapolation q (ne_of_gt (lt_trans zero_lt_one hq)) c
  have hfinite := (abs_le.mp (hc (0 : ℕ))).2
  have hinfty := (abs_le.mp (hc ∞)).1
  rw [hmax] at he
  have h₁ := mul_nonneg (le_of_lt (lt_trans zero_lt_one hq)) (sub_nonneg.mpr hfinite)
  have h₂ := mul_nonneg (sub_nonneg.mpr hq.le) (sub_nonneg.mpr hinfty)
  nlinarith

theorem gamma_zero (q : ℝ) (hq : 1 < q) : gamma q 0 = q⁻¹ := by
  rw [gamma_eq_extremalValue q hq 0, extremalValue_zero q hq]
  field_simp
  ring

theorem gamma_le_inverse (q : ℝ) (hq : 1 < q) (r : ℕ) : gamma q r ≤ q⁻¹ := by
  rw [gamma_eq_extremalValue q hq r, inv_eq_one_div]
  have hB := one_lt_extremalValue q hq r
  apply (div_le_div_iff₀ (by linarith : 0 < 1+extremalValue q r)
    (lt_trans zero_lt_one hq)).mpr
  have h := extremalValue_lower q hq r
  linarith

end LocalCertification.Extremal
