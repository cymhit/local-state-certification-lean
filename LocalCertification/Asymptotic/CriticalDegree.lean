import LocalCertification.Asymptotic.SharpRate
import Mathlib.Order.Lattice.Nat

open scoped Topology
open Filter Set Real

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The sharp estimate implies convergence for all q>1, including q<=2. -/
theorem gamma_tendsto_zero (q : ℝ) (hq : 1 < q) : Tendsto (LocalCertification.Extremal.gamma q) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have ha0 : 0 ≤ q⁻¹ := (inv_pos.mpr hq0).le
  have ha1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).mpr hq
  have hC := upperRateConstant_pos q hq
  have hgeo : Tendsto (fun r : ℕ => upperRateConstant q * (q⁻¹) ^ r) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1))
  apply squeeze_zero' (Filter.Eventually.of_forall (LocalCertification.Extremal.gamma_nonneg q hq)) _ hgeo
  filter_upwards [eventually_ge_atTop 2] with r hr
  apply (gamma_rate_upper q hq r hr).trans
  have hs : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ r by omega))
  exact div_le_self (by positivity) hs

theorem exists_degree_for_positive_gap (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g) :
    ∃ r : ℕ, LocalCertification.Extremal.gamma q r < g :=
  ((tendsto_order.mp (gamma_tendsto_zero q hq)).2 g hg).exists

/-- The exact strict-threshold minimum from the paper, as a total function of the gap. -/
def criticalDegree (q g : ℝ) : ℕ := sInf {r : ℕ | LocalCertification.Extremal.gamma q r < g}

theorem criticalDegree_spec (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g) :
    LocalCertification.Extremal.gamma q (criticalDegree q g) < g :=
  Nat.sInf_mem (exists_degree_for_positive_gap q hq g hg)

theorem criticalDegree_le_iff (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g) (r : ℕ) :
    criticalDegree q g ≤ r ↔ LocalCertification.Extremal.gamma q r < g := by
  constructor
  · intro hr
    exact ((LocalCertification.Extremal.gamma_strictAnti q hq).antitone hr).trans_lt (criticalDegree_spec q hq g hg)
  · intro hr
    exact Nat.sInf_le hr

theorem lt_criticalDegree_iff (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g) (r : ℕ) :
    r < criticalDegree q g ↔ g ≤ LocalCertification.Extremal.gamma q r := by
  rw [← not_le, criticalDegree_le_iff q hq g hg r, not_lt]

theorem criticalDegree_bracket (q : ℝ) (hq : 1 < q) (g : ℝ) (hg : 0 < g)
    (hk : 0 < criticalDegree q g) :
    LocalCertification.Extremal.gamma q (criticalDegree q g) < g ∧
      g ≤ LocalCertification.Extremal.gamma q (criticalDegree q g - 1) := by
  exact ⟨criticalDegree_spec q hq g hg,
    (lt_criticalDegree_iff q hq g hg _).1 (by omega)⟩

/-- At equality, the critical index advances to the next degree, including j=0. -/
theorem criticalDegree_at_critical_value (q : ℝ) (hq : 1 < q) (j : ℕ) :
    criticalDegree q (LocalCertification.Extremal.gamma q j) = j + 1 := by
  have hg := LocalCertification.Extremal.gamma_pos q hq j
  have hle := (criticalDegree_le_iff q hq _ hg (j + 1)).2 (LocalCertification.Extremal.gamma_strict_succ q hq j)
  have hlt := (lt_criticalDegree_iff q hq _ hg j).2 le_rfl
  omega

theorem criticalDegree_tendsto_atTop (q : ℝ) (hq : 1 < q) :
    Tendsto (criticalDegree q) (𝓝[>] (0 : ℝ)) atTop := by
  apply tendsto_atTop.2
  intro n
  have hsmall : ∀ᶠ g : ℝ in 𝓝[>] (0 : ℝ), g < LocalCertification.Extremal.gamma q n :=
    (eventually_lt_nhds (LocalCertification.Extremal.gamma_pos q hq n)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with g hg hsmallg
  exact ((lt_criticalDegree_iff q hq g hg n).2 hsmallg.le).le

end LocalCertification.Asymptotic
