import LocalCertification.Asymptotic.RootLimit

open scoped Topology
open Filter Set Real

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section
namespace LocalCertification.Asymptotic

def logarithmicGap (q g : ℝ) : ℝ := Real.log g⁻¹ / Real.log q

def degreeLogModel (q x : ℝ) : ℝ := x + Real.log x / (2 * Real.log q)

def inversionBound (q : ℝ) : ℝ :=
  |Real.log (lowerRateConstant q) / Real.log q| + |Real.log (upperRateConstant q) / Real.log q| +
    1 + Real.log 2 / (2 * Real.log q)

theorem inversionBound_nonneg (q : ℝ) (hq : 1 < q) : 0 ≤ inversionBound q := by
  have hlog := Real.log_pos hq
  unfold inversionBound
  positivity

/-- Taking logarithms retains the strict lower bracket at the actual critical index. -/
theorem criticalDegree_log_bracket (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g)
    (hk : 3 ≤ criticalDegree q g) :
    logarithmicGap q g + Real.log (lowerRateConstant q) / Real.log q <
        degreeLogModel q (criticalDegree q g) ∧
    degreeLogModel q ((criticalDegree q g - 1 : ℕ) : ℝ) ≤
      logarithmicGap q g + Real.log (upperRateConstant q) / Real.log q := by
  let k := criticalDegree q g
  have hlog := Real.log_pos hq
  have hbr := criticalDegree_bracket q hq g hg (by omega)
  have hlo := (gamma_log_bounds q hq k (by omega)).1
  have hup := (gamma_log_bounds q hq (k - 1) (by omega)).2
  have hlstrict := Real.log_lt_log (LocalCertification.Extremal.gamma_pos q hq k) hbr.1
  have hupper := (Real.log_le_log_iff hg (LocalCertification.Extremal.gamma_pos q hq (k - 1))).2 hbr.2
  constructor
  · have hh : Real.log (lowerRateConstant q) - Real.log g <
        (k : ℝ) * Real.log q + Real.log k / 2 := by linarith
    have hh' := (div_lt_div_iff_of_pos_right hlog).2 hh
    convert hh' using 1 <;> dsimp [logarithmicGap, degreeLogModel, k]
    · rw [Real.log_inv]; ring
    · field_simp
  · have hh : ((k - 1 : ℕ) : ℝ) * Real.log q + Real.log ((k - 1 : ℕ) : ℝ) / 2 ≤
        Real.log (upperRateConstant q) - Real.log g := by linarith
    have hh' := (div_le_div_iff_of_pos_right hlog).2 hh
    convert hh' using 1 <;> dsimp [logarithmicGap, degreeLogModel, k]
    · field_simp
    · rw [Real.log_inv]; ring

theorem degreeLogModel_step_bound (q : ℝ) (hq : 1 < q) (k : ℕ) (hk : 2 ≤ k) :
    degreeLogModel q k - degreeLogModel q ((k - 1 : ℕ) : ℝ) ≤
      1 + Real.log 2 / (2 * Real.log q) := by
  have hlog := Real.log_pos hq
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkm : 0 < (k : ℝ) - 1 := by linarith
  have hlogdiff : Real.log (k : ℝ) - Real.log ((k : ℝ) - 1) ≤ Real.log 2 := by
    rw [← Real.log_div hk0.ne' hkm.ne']
    apply (Real.log_le_log_iff (div_pos hk0 hkm) (by norm_num : (0 : ℝ) < 2)).2
    apply (div_le_iff₀ hkm).2
    linarith
  have he : degreeLogModel q k - degreeLogModel q ((k - 1 : ℕ) : ℝ) =
      1 + (Real.log (k : ℝ) - Real.log ((k : ℝ) - 1)) / (2 * Real.log q) := by
    unfold degreeLogModel
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  rw [he]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hlogdiff (by positivity))

/-- An explicit bounded error for the implicit inverse relation, valid once k>=3. -/
theorem criticalDegree_implicit_bound (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g)
    (hk : 3 ≤ criticalDegree q g) :
    |degreeLogModel q (criticalDegree q g) - logarithmicGap q g| ≤ inversionBound q := by
  have hb := criticalDegree_log_bracket q hq g hg hk
  have hs := degreeLogModel_step_bound q hq (criticalDegree q g) (by omega)
  have hlog := Real.log_pos hq
  have hz : 0 ≤ Real.log 2 / (2 * Real.log q) := by positivity
  unfold inversionBound
  rw [abs_le]
  constructor
  · have h := neg_abs_le (Real.log (lowerRateConstant q) / Real.log q)
    linarith [abs_nonneg (Real.log (upperRateConstant q) / Real.log q), hb.1]
  · have h := le_abs_self (Real.log (upperRateConstant q) / Real.log q)
    linarith [abs_nonneg (Real.log (lowerRateConstant q) / Real.log q), hb.2]

theorem criticalDegree_implicit_eventually (q : ℝ) (hq : 1 < q) :
    ∀ᶠ g : ℝ in 𝓝[>] (0 : ℝ),
      |degreeLogModel q (criticalDegree q g) - logarithmicGap q g| ≤ inversionBound q := by
  filter_upwards [self_mem_nhdsWithin,
    (criticalDegree_tendsto_atTop q hq).eventually (eventually_ge_atTop 3)] with g hg hk
  exact criticalDegree_implicit_bound q hq g hg hk

end LocalCertification.Asymptotic
