import LocalCertification.Protocol.FixedBlockHierarchy

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The paper's explicit block size, rounded up once and fixed for every copy and system size. -/
def sufficientBlockSize (g : ℝ) : ℕ := max 1 ⌈Real.log (1/g)/Real.log 2⌉₊

theorem sufficientBlockSize_positive (g : ℝ) : 1≤sufficientBlockSize g := le_max_left _ _

/-- Every positive gap admits that fixed finite block size strictly above the constant-budget threshold. -/
theorem sufficientBlockSize_threshold (g : ℝ) (hg : 0<g) :
    1/(((2^(sufficientBlockSize g) : ℕ):ℝ)+1)<g := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hr : Real.log (1/g)/Real.log 2≤(sufficientBlockSize g : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈Real.log (1/g)/Real.log 2⌉₊))
  have hl := (div_le_iff₀ hlog2).mp hr
  have hp : 1/g≤(2:ℝ)^sufficientBlockSize g := by
    calc
      _ = Real.exp (Real.log (1/g)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp ((sufficientBlockSize g : ℝ)*Real.log 2) := Real.exp_le_exp.mpr hl
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hpg : 1≤(2:ℝ)^sufficientBlockSize g*g := (div_le_iff₀ hg).mp hp
  have hd : 0<(((2^sufficientBlockSize g : ℕ):ℝ)+1) := by positivity
  apply (div_lt_iff₀ hd).mpr
  push_cast
  nlinarith

/-- A precise O(1+log(1/g)) bound, with max0 retaining validity also for g>1. -/
theorem sufficientBlockSize_log_bound (g : ℝ) :
    (sufficientBlockSize g : ℝ)≤1+max 0 (Real.log (1/g)/Real.log 2) := by
  let a := Real.log (1/g)/Real.log 2
  change ((max 1 ⌈a⌉₊ : ℕ):ℝ)≤1+max 0 a
  rw [Nat.cast_max]
  norm_num only [Nat.cast_one]
  apply max_le
  · linarith [le_max_left (0:ℝ) a]
  · by_cases ha : 0≤a
    · have hc := (Nat.ceil_lt_add_one ha).le
      rw [max_eq_right ha]
      linarith
    · have hc : ⌈a⌉₊=0 := Nat.ceil_eq_zero.mpr (le_of_not_ge ha)
      rw [hc]
      norm_num only [Nat.cast_zero]
      linarith [le_max_left (0:ℝ) a]

/-- Above threshold, the explicit block choice really has original critical exponent zero. -/
theorem sufficientBlockSize_degree_zero (g : ℝ) (hg : 0<g) :
    criticalDegree (((2^sufficientBlockSize g : ℕ):ℝ)+1) g=0 :=
  (fixedBlock_degree_zero_iff _ (sufficientBlockSize_positive g) g hg).mpr (sufficientBlockSize_threshold g hg)

/-- Positive critical degree forces any actual budget with the proved lower bound to diverge,
even when the target varies arbitrarily within the common good sets. -/
theorem polynomial_log_budget_diverges (r : ℕ) (hr : 1≤r) (c δ : ℝ)
    (hc : 0<c) (hδ : 0<δ) (hδ1 : δ<1) (f : ℕ → ℝ≥0∞)
    (hbound : ∀ᶠ m : ℕ in atTop,ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤f m) :
    Tendsto f atTop (nhds ∞) := by
  have hlog : 0<Real.log (1/δ) := Real.log_pos ((one_lt_div hδ).mpr hδ1)
  have hp : Tendsto (fun m : ℕ => (m:ℝ)^r) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
    simpa only [pow_one] using pow_le_pow_right₀ hm1 hr
  have hreal : Tendsto (fun m : ℕ => c*(m:ℝ)^r*Real.log (1/δ)) atTop atTop :=
    (hp.const_mul_atTop hc).atTop_mul_const hlog
  have hlim := ENNReal.tendsto_ofReal_atTop.comp hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hbound
    (Filter.Eventually.of_forall (fun _ => le_top))

end LocalCertification.Protocol
