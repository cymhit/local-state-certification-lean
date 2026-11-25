import LocalCertification.Asymptotic.WienerInterpolationLower
import LocalCertification.Asymptotic.WienerInterpolationUpper
import LocalCertification.Extremal.DimensionParameters

/-! # Sharp order from repeated-node Wiener interpolation -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Topology
open Filter Asymptotics
noncomputable section
namespace LocalCertification.Asymptotic.Wiener

/-- Both interpolation estimates are transferred to the positive-integer envelope
problem through the augmented-norm identity, with constants independent of degree. -/
theorem gamma_sharp_order (q : ℝ) (hq : 1 < q) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ r : ℕ, 2 ≤ r →
      l * q⁻¹ ^ r / Real.sqrt r ≤ Extremal.gamma q r ∧
      Extremal.gamma q r ≤ u * q⁻¹ ^ r / Real.sqrt r := by
  let a := q⁻¹
  have ha : 0 < a := inv_pos.mpr (by linarith)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hq
  obtain ⟨c, hc, hlo⟩ := szehr_zarouf_lower a ha ha1
  let E := Real.sqrt (Real.exp 1)
  have hE : 0 < E := Real.sqrt_pos.mpr (Real.exp_pos _)
  refine ⟨a / (1 + 2*E), 2*a/c, by positivity, by positivity, ?_⟩
  intro r hr
  let A := a ^ (r + 1)
  let R := Real.sqrt r
  let S := Real.sqrt (r + 1 : ℕ)
  let B := Extremal.extremalValue q r
  have hA : 0 < A := pow_pos ha _
  have hAle : A ≤ 1 := pow_le_one₀ ha.le ha1.le
  have hR1 : 1 ≤ R := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ r by omega))
  have hR : 0 < R := by linarith
  have hRS : R ≤ S := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ r)
  have hS : S ≤ 2*R := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have h1 := Real.sq_sqrt (show 0 ≤ (r : ℝ) by positivity)
    have h2 := Real.sq_sqrt (show 0 ≤ ((r + 1 : ℕ) : ℝ) by positivity)
    push_cast at h2
    dsimp only [S, R]
    push_cast
    nlinarith [Real.sqrt_nonneg (r : ℝ)]
  have hB1 : 0 < 1+B := by have := Extremal.one_lt_extremalValue q hq r; dsimp [B]; linarith
  obtain ⟨hb₁, hb₂⟩ := interpolation_sandwich q hq r
  change A⁻¹ * phi a r ≤ B at hb₁
  change B ≤ 2*A⁻¹*phi a r + 1 at hb₂
  have hu := schaffer_upper a ha ha1 r
  rw [Real.sqrt_mul (Real.exp_pos _).le] at hu
  change phi a r ≤ E*S at hu
  have hl := hlo r
  change c*S ≤ phi a r at hl
  have hcrossL : c*R ≤ A*(1+B) := by
    have h := mul_le_mul_of_nonneg_left hb₁ hA.le
    rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at h
    linarith [mul_le_mul_of_nonneg_left hRS hc.le]
  have hcrossU : A*(1+B) ≤ 2*((1+2*E)*R) := by
    have h := mul_le_mul_of_nonneg_left hb₂ hA.le
    ring_nf at h
    have hcancel : A * (phi a r * A⁻¹) = phi a r := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hS hE.le, hcancel]
  rw [Extremal.gamma_eq_extremalValue q hq r]
  change a/(1+2*E) * a^r/R ≤ 2/(1+B) ∧ 2/(1+B) ≤ 2*a/c * a^r/R
  have hL : a/(1+2*E) * a^r/R = A/((1+2*E)*R) := by
    dsimp only [A]
    rw [pow_succ, div_mul_eq_div_div]
    ring
  have hU : 2*a/c * a^r/R = 2*A/(c*R) := by
    dsimp only [A]
    rw [pow_succ, div_mul_eq_div_div]
    ring
  rw [hL, hU]
  exact ⟨(div_le_div_iff₀ (by positivity) hB1).mpr hcrossU,
    (div_le_div_iff₀ hB1 (by positivity)).mpr (by linarith)⟩

end LocalCertification.Asymptotic.Wiener
