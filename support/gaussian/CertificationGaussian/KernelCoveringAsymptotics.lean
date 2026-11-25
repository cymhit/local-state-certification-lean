import CertificationGaussian.TailAsymptotics

/-! The exact cardinality of the actual local-frame covering is at most a
quadratic exponential. Signed weights and support containing zero are allowed. -/
set_option autoImplicit false
open Filter
open scoped BigOperators Topology
noncomputable section
namespace CertificationGaussian

theorem kernelCovering_eventually_quadratic {d : ℕ} (hd : 2 ≤ d) (J : Finset ℕ)
    (θ : ℕ → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      (1 + 2 * (d : ℝ)^n * (kernelWeightL1 J θ)^2 * (n : ℝ)^2 /
        kernelVarianceScale d n J θ) ^ (2 * d^4 * n) ≤
          Real.exp (A * (n : ℝ)^2) := by
  let c := kernelOrderLowerConstant d J θ hθ
  let s := effectiveKernelOrder J θ hθ
  let L := kernelWeightL1 J θ
  let C := 1 + 2 * L^2 / c
  let A := 2 * (d : ℝ)^4 * (Real.log d + 1)
  have hc : 0 < c := kernelOrderLowerConstant_pos hd J θ hθ
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans hdR
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos hdR
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  filter_upwards [eventually_polynomial_le_exp C (s+2) (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (max 1 (2 * J.sup id))] with n hpoly hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hv : c / (n : ℝ)^s ≤ kernelVarianceScale d n J θ :=
    (kernelVarianceScale_order_bounds hd J θ hθ hn).1
  have hv0 : 0 < kernelVarianceScale d n J θ := (div_pos hc (pow_pos hn0 s)).trans_le hv
  have hterm : 2 * (d : ℝ)^n * L^2 * (n : ℝ)^2 / kernelVarianceScale d n J θ ≤
      (2 * L^2 / c) * (d : ℝ)^n * (n : ℝ)^(s+2) := by
    calc
      _ ≤ (2 * (d : ℝ)^n * L^2 * (n : ℝ)^2) / (c / (n : ℝ)^s) :=
        div_le_div_of_nonneg_left (by positivity) (div_pos hc (pow_pos hn0 s)) hv
      _ = _ := by
        rw [pow_add]
        field_simp
  have h1 : (1 : ℝ) ≤ (d : ℝ)^n * (n : ℝ)^(s+2) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (one_le_pow₀ hdR.le) (one_le_pow₀ hnR)
        (by norm_num) (by positivity)
  have hbase : 1 + 2 * (d : ℝ)^n * L^2 * (n : ℝ)^2 / kernelVarianceScale d n J θ ≤
      Real.exp ((Real.log d + 1) * (n : ℝ)) := by
    calc
      _ ≤ (d : ℝ)^n * (n : ℝ)^(s+2) + (2 * L^2 / c) * (d : ℝ)^n * (n : ℝ)^(s+2) :=
        add_le_add h1 hterm
      _ = (d : ℝ)^n * (C * (n : ℝ)^(s+2)) := by dsimp [C]; ring
      _ ≤ (d : ℝ)^n * Real.exp (1 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hpoly (pow_nonneg hd0.le n)
      _ = _ := by
        have he : (d : ℝ)^n = Real.exp ((n : ℝ) * Real.log d) := by
          rw [Real.exp_nat_mul, Real.exp_log hd0]
        rw [he, ← Real.exp_add]
        congr 1
        ring
  calc
    _ ≤ (Real.exp ((Real.log d + 1) * (n : ℝ))) ^ (2 * d^4 * n) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [A]
      push_cast
      ring

end CertificationGaussian
