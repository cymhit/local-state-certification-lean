import LocalCertification.Asymptotic.LogarithmicInversion
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped Topology
open Filter Set Real Asymptotics

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The sharp-order statement in the paper's real-power notation. -/
theorem sharp_order (q : ℝ) (hq : 1 < q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      c * q ^ (-(r : ℝ)) / Real.sqrt r ≤ LocalCertification.Extremal.gamma q r ∧
      LocalCertification.Extremal.gamma q r ≤ C * q ^ (-(r : ℝ)) / Real.sqrt r := by
  refine ⟨lowerRateConstant q, upperRateConstant q, lowerRateConstant_pos q hq,
    upperRateConstant_pos q hq, ?_⟩
  intro r hr
  simpa only [LocalCertification.Extremal.inverse_pow_eq_real_decay] using gamma_sharp_rate q hq r hr

theorem logarithmicGap_eq_logb (q g : ℝ) : logarithmicGap q g = Real.logb q g⁻¹ := rfl

/-- The exact original minimum obeys L-(1/2)log_q L+O_q(1), L=log_q(1/g). -/
theorem criticalDegree_logb_inversion (q : ℝ) (hq : 1 < q) :
    (fun g : ℝ => (criticalDegree q g : ℝ) -
      (Real.logb q g⁻¹ - (1 / 2) * Real.logb q (Real.logb q g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
  convert criticalDegree_logarithmic_inversion q hq using 1
  funext g
  unfold logarithmicGap Real.logb
  ring

/-- Sharp critical-sequence order and logarithmic inversion for every fixed real q>1. -/
theorem sharp_order_and_inversion (q : ℝ) (hq : 1 < q) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      c * q ^ (-(r : ℝ)) / Real.sqrt r ≤ LocalCertification.Extremal.gamma q r ∧
      LocalCertification.Extremal.gamma q r ≤ C * q ^ (-(r : ℝ)) / Real.sqrt r) ∧
    ((fun g : ℝ => (criticalDegree q g : ℝ) -
      (Real.logb q g⁻¹ - (1 / 2) * Real.logb q (Real.logb q g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ))) :=
  ⟨sharp_order q hq, criticalDegree_logb_inversion q hq⟩

theorem qudit_base_gt_one (d : ℕ) (hd : 2 ≤ d) : 1 < (d : ℝ) + 1 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- Actual q=d+1 specialization, including composite dimensions. -/
theorem qudit_sharp_order (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      c * ((d : ℝ) + 1) ^ (-(r : ℝ)) / Real.sqrt r ≤ LocalCertification.Extremal.gamma ((d : ℝ) + 1) r ∧
      LocalCertification.Extremal.gamma ((d : ℝ) + 1) r ≤ C * ((d : ℝ) + 1) ^ (-(r : ℝ)) / Real.sqrt r :=
  sharp_order ((d : ℝ) + 1) (qudit_base_gt_one d hd)

theorem qudit_logarithmic_inversion (d : ℕ) (hd : 2 ≤ d) :
    (fun g : ℝ => (criticalDegree ((d : ℝ) + 1) g : ℝ) -
      (Real.logb ((d : ℝ) + 1) g⁻¹ - (1 / 2) *
        Real.logb ((d : ℝ) + 1) (Real.logb ((d : ℝ) + 1) g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
  criticalDegree_logb_inversion ((d : ℝ) + 1) (qudit_base_gt_one d hd)

theorem qudit_root_limit (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (fun r : ℕ => (LocalCertification.Extremal.gamma ((d : ℝ) + 1) r) ^ (1 / (r : ℝ)))
      atTop (𝓝 (((d : ℝ) + 1)⁻¹)) :=
  gamma_root_limit ((d : ℝ) + 1) (qudit_base_gt_one d hd)

theorem qudit_critical_boundary (d : ℕ) (hd : 2 ≤ d) (j : ℕ) :
    criticalDegree ((d : ℝ) + 1) (LocalCertification.Extremal.gamma ((d : ℝ) + 1) j) = j + 1 :=
  criticalDegree_at_critical_value ((d : ℝ) + 1) (qudit_base_gt_one d hd) j

end LocalCertification.Asymptotic
