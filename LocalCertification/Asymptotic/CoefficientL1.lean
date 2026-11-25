import LocalCertification.Asymptotic.WeightedSquares
import LocalCertification.Asymptotic.WeightKernel

open scoped BigOperators Topology
open MeasureTheory AddCircle Complex Finset

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The weighted energy entering the exact coefficient bound. -/
theorem blaschkeCoeff_hasSum_energy (a : ℝ) (ha : |a| < 1) (s : ℕ) (hs : 1 ≤ s) :
    HasSum (fun n : ℕ => (1 + ((n : ℝ) / s) ^ 2) * blaschkeCoeff a s n ^ 2)
      (2 / (1 - a ^ 2)) := by
  have hs0 := blaschkeCoeff_hasSum_sq a ha s
  have hs1 := (blaschkeCoeff_hasSum_weighted_sq a ha s).mul_left ((s : ℝ) ^ 2)⁻¹
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hane : 1 - a ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one a).mpr ha))
  convert hs0.add hs1 using 1
  · funext n
    field_simp
  · field_simp
    ring

/-- Weighted Cauchy--Schwarz, derived from finite sums and nonnegative partial sums. -/
theorem tsum_abs_le_weighted_sqrt (c w : ℕ → ℝ) (W : ℝ)
    (hw : ∀ n, 0 < w n) (hW : HasSum (fun n => w n * c n ^ 2) W)
    (hInv : Summable (fun n => (w n)⁻¹)) :
    (∑' n, |c n|) ≤ Real.sqrt W * Real.sqrt (∑' n, (w n)⁻¹) := by
  apply tsum_le_of_sum_le' (by positivity)
  intro u
  have hf (n : ℕ) : 0 ≤ w n * c n ^ 2 := mul_nonneg (hw n).le (sq_nonneg _)
  have hg (n : ℕ) : 0 ≤ (w n)⁻¹ := inv_nonneg.mpr (hw n).le
  have he (n : ℕ) : |c n| = Real.sqrt (w n * c n ^ 2) * Real.sqrt ((w n)⁻¹) := by
    rw [← Real.sqrt_mul (hf n)]
    have hmul : (w n * c n ^ 2) * (w n)⁻¹ = c n ^ 2 := by field_simp [ne_of_gt (hw n)]
    rw [hmul, Real.sqrt_sq_eq_abs]
  have hleft : (∑ n ∈ u, w n * c n ^ 2) ≤ W :=
    sum_le_hasSum u (fun n _ => hf n) hW
  have hright : (∑ n ∈ u, (w n)⁻¹) ≤ ∑' n, (w n)⁻¹ :=
    Summable.sum_le_tsum u (fun n _ => hg n) hInv
  calc
    (∑ n ∈ u, |c n|) = ∑ n ∈ u, Real.sqrt (w n * c n ^ 2) * Real.sqrt ((w n)⁻¹) :=
      Finset.sum_congr rfl (fun n _ => he n)
    _ ≤ Real.sqrt (∑ n ∈ u, w n * c n ^ 2) * Real.sqrt (∑ n ∈ u, (w n)⁻¹) :=
      Real.sum_sqrt_mul_sqrt_le u hf hg
    _ ≤ Real.sqrt W * Real.sqrt (∑' n, (w n)⁻¹) :=
      mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The square-root bound for the absolute sum of the Blaschke coefficients. -/
theorem blaschkeCoeff_tsum_abs_le (a : ℝ) (ha : |a| < 1) (s : ℕ) (hs : 1 ≤ s) :
    (∑' n, |blaschkeCoeff a s n|) ≤
      Real.sqrt ((2 + Real.pi) / (1 - a ^ 2)) * Real.sqrt s := by
  have hspos : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hapos : 0 < 1 - a ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one a).mpr ha)
  have h := tsum_abs_le_weighted_sqrt (blaschkeCoeff a s)
    (fun n : ℕ => 1 + ((n : ℝ) / s) ^ 2) (2 / (1 - a ^ 2))
    (fun _ => by positivity) (blaschkeCoeff_hasSum_energy a ha s hs)
    (weightKernel_summable s hspos)
  have hb := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (weightKernel_tsum_le_scaled s hs))
    (Real.sqrt_nonneg (2 / (1 - a ^ 2)))
  have he : Real.sqrt (2 / (1 - a ^ 2)) * Real.sqrt (((2 + Real.pi) / 2) * s) =
      Real.sqrt ((2 + Real.pi) / (1 - a ^ 2)) * Real.sqrt s := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 / (1 - a ^ 2)),
      ← Real.sqrt_mul (by positivity : 0 ≤ (2 + Real.pi) / (1 - a ^ 2))]
    congr 1
    ring
  exact h.trans (hb.trans_eq he)

/-- The Blaschke coefficient bound's constant expressed in terms of the decay base. -/
def blaschkeCoefficientConstant (q : ℝ) : ℝ :=
  Real.sqrt ((2 + Real.pi) / (1 - (q⁻¹) ^ 2))

theorem blaschkeCoeff_tsum_abs_le_q (q : ℝ) (hq : 1 < q) (s : ℕ) (hs : 1 ≤ s) :
    (∑' n, |blaschkeCoeff (q⁻¹) s n|) ≤ blaschkeCoefficientConstant q * Real.sqrt s := by
  have haq : |q⁻¹| < 1 := by rw [abs_of_pos (inv_pos.mpr (by linarith))]; exact inv_lt_one_of_one_lt₀ hq
  exact blaschkeCoeff_tsum_abs_le (q⁻¹) haq s hs

theorem blaschkeCoefficientConstant_pos (q : ℝ) (hq : 1 < q) :
    0 < blaschkeCoefficientConstant q := by
  have haq : |q⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hq
  have hden : 0 < 1 - (q⁻¹) ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one (q⁻¹)).mpr haq)
  unfold blaschkeCoefficientConstant
  apply Real.sqrt_pos.mpr
  exact div_pos (by positivity) hden

end LocalCertification.Asymptotic
