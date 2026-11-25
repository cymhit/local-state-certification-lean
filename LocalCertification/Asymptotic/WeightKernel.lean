import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open scoped BigOperators Topology
open MeasureTheory Set Real

set_option autoImplicit false

noncomputable section
namespace LocalCertification.Asymptotic

/-- Reciprocal quadratic weight used in the sharp coefficient estimate. -/
def weightKernel (s x : ℝ) : ℝ := (1 + (x / s) ^ 2)⁻¹

theorem weightKernel_nonneg (s x : ℝ) : 0 ≤ weightKernel s x := by
  unfold weightKernel
  positivity

theorem weightKernel_antitoneOn (s : ℝ) (hs : 0 < s) :
    AntitoneOn (weightKernel s) (Ici 0) := by
  intro x hx y hy hxy
  change (1 + (y / s) ^ 2)⁻¹ ≤ (1 + (x / s) ^ 2)⁻¹
  apply inv_anti₀ (by positivity)
  have hd : 0 ≤ x / s := div_nonneg hx hs.le
  have he : x / s ≤ y / s := div_le_div_of_nonneg_right hxy hs.le
  nlinarith

theorem weightKernel_integrable (s : ℝ) (hs : 0 < s) : Integrable (weightKernel s) := by
  change Integrable (fun x : ℝ => (1 + (x / s) ^ 2)⁻¹)
  simpa only [div_eq_mul_inv, mul_comm] using
    integrable_inv_one_add_mul_sq (inv_ne_zero hs.ne')

theorem weightKernel_integral_Ioi (s : ℝ) (hs : 0 < s) :
    (∫ x in Ioi 0, weightKernel s x) = Real.pi * s / 2 := by
  have he := integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0
    (inv_pos.mpr hs)
  simpa only [weightKernel, div_eq_mul_inv, mul_comm, inv_inv, mul_zero,
    integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul, mul_assoc] using he

theorem weightKernel_summable (s : ℝ) (hs : 0 < s) :
    Summable (fun n : ℕ => weightKernel s n) :=
  (weightKernel_antitoneOn s hs).summable_of_integrableOn_Ioi_zero
    (weightKernel_integrable s hs).integrableOn (fun x _ => weightKernel_nonneg s x)

theorem weightKernel_tsum_le (s : ℝ) (hs : 0 < s) :
    (∑' n : ℕ, weightKernel s n) ≤ 1 + Real.pi * s / 2 := by
  have h := (weightKernel_antitoneOn s hs).tsum_le_integral
    (weightKernel_integrable s hs).integrableOn (fun x _ => weightKernel_nonneg s x)
  rw [weightKernel_integral_Ioi s hs] at h
  simpa only [weightKernel, zero_div, zero_pow (by decide : 2 ≠ 0),
    add_zero, inv_one] using h

theorem weightKernel_tsum_le_scaled (s : ℕ) (hs : 1 ≤ s) :
    (∑' n : ℕ, weightKernel s n) ≤ ((2 + Real.pi) / 2) * s := by
  have hs' : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  have h := weightKernel_tsum_le s (by linarith)
  linarith

end LocalCertification.Asymptotic
