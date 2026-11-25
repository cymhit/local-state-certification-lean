import LocalCertification.Protocol.PowerLowerBound
import LocalCertification.Protocol.UpperBound
import LocalCertification.Asymptotic.CriticalDegree

set_option autoImplicit false
open MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- One explicit real failure rate for the union of the actual upper- and lower-bound target events. -/
def hierarchyFailure (r : ℕ) (C c : ℝ) (n : ℕ) : ℝ :=
  C*((n:ℝ)^8)⁻¹+(r:ℝ)/(n:ℝ)^3+Real.exp (-c*(n:ℝ)^3)

theorem hierarchyFailure_nonneg (r : ℕ) (C c : ℝ) (hC : 0≤C) (n : ℕ) :
    0≤hierarchyFailure r C c n := by unfold hierarchyFailure; positivity

theorem hierarchyFailure_tendsto (r : ℕ) (C c : ℝ) (hc : 0<c) :
    Tendsto (hierarchyFailure r C c) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h8 : Tendsto (fun n : ℕ => C*((n:ℝ)^8)⁻¹) atTop (nhds 0) := by
    simpa only [inv_pow,zero_pow (by omega : 8≠0),mul_zero] using tendsto_const_nhds.mul (hinv.pow 8)
  have h3 : Tendsto (fun n : ℕ => (r:ℝ)/(n:ℝ)^3) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,inv_pow,zero_pow (by omega : 3≠0),mul_zero] using
      tendsto_const_nhds.mul (hinv.pow 3)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-c*(n:ℝ)^3)) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)) _
      (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-c)).le
        (Real.exp_lt_one_iff.mpr (by linarith : -c<0)))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1:ℝ)≤n := by exact_mod_cast hn
    have hpow : (n:ℝ)≤(n:ℝ)^3 := by
      calc
        (n:ℝ)=(n:ℝ)*1 := by ring
        _≤(n:ℝ)*(n:ℝ)^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hn') (Nat.cast_nonneg n)
        _=(n:ℝ)^3 := by ring
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  change Tendsto (fun n : ℕ => C*((n:ℝ)^8)⁻¹+(r:ℝ)/(n:ℝ)^3+Real.exp (-c*(n:ℝ)^3)) atTop (nhds 0)
  simpa only [add_zero] using (h8.add h3).add hexp

/-- The actual expected and every-path capped budgets have the critical polynomial order, on one
measurable Haar event for all error levels simultaneously. This includes critical equality and degree
zero. The failure rate is explicit and tends to zero; no operator or information premises are supplied. -/
theorem qudit_budget_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C Cbad cdecay : ℝ,0<c ∧ 0<C ∧ 0<Cbad ∧ 0<cdecay ∧
      Tendsto (hierarchyFailure r Cbad cdecay) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (hierarchyFailure r Cbad cdecay n) ∧
        ∀ U,U∉bad → ∀ δ : ℝ,0<δ → δ≤1/3 →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (haarPureVector ψ₀ U) a b δ ∧
          expectedBudget (haarPureVector ψ₀ U) a b δ≤ENat.toENNReal (maximumBudget (haarPureVector ψ₀ U) a b δ) ∧
          ENat.toENNReal (maximumBudget (haarPureVector ψ₀ U) a b δ)≤
            ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  have hb1 : b<1 := hab.trans_le ha
  have hq : 1<(d:ℝ)+1 := by
    have : (2:ℝ)≤d := by exact_mod_cast hd
    linarith
  have hg : 0<(a-b)/(1-b) := div_pos (sub_pos.mpr hab) (sub_pos.mpr hb1)
  have hupper : gamma ((d:ℝ)+1) r<(a-b)/(1-b) := criticalDegree_spec _ hq _ hg
  have hlower : r=0 ∨ (a-b)/(1-b)≤gamma ((d:ℝ)+1) (r-1) := by
    by_cases hr : r=0
    · exact Or.inl hr
    · exact Or.inr (criticalDegree_bracket _ hq _ hg (by omega : 0<r)).2
  obtain ⟨C,Cbad,hC,hCbad,hup⟩ := qudit_budget_upper d r hd a b ha hb.le hb1 hupper
  obtain ⟨c,cdecay,hc,hdecay,hlo⟩ := qudit_budget_power_lower d r hd a b ha hb hb1 hlower
  refine ⟨c,C,Cbad,cdecay,hc,hC,hCbad,hdecay,hierarchyFailure_tendsto r Cbad cdecay hdecay,?_⟩
  filter_upwards [hup,hlo] with n hnup hnlo
  intro ψ₀
  obtain ⟨badup,hmup,hpup,hupper⟩ := hnup ψ₀
  obtain ⟨badlo,hmlo,hplo,hlower⟩ := hnlo ψ₀
  refine ⟨badup∪badlo,hmup.union hmlo,?_,?_⟩
  · calc
      complexUnitaryHaar (QuditIndex d n) (badup∪badlo)≤
          complexUnitaryHaar (QuditIndex d n) badup+complexUnitaryHaar (QuditIndex d n) badlo :=
        measure_union_le _ _
      _≤ENNReal.ofReal (Cbad*((n:ℝ)^8)⁻¹)+
          (ENNReal.ofReal ((r:ℝ)/(n:ℝ)^3)+ENNReal.ofReal (Real.exp (-cdecay*(n:ℝ)^3))) :=
        add_le_add hpup hplo
      _=ENNReal.ofReal (hierarchyFailure r Cbad cdecay n) := by
        unfold hierarchyFailure
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
        ac_rfl
  · intro U hU δ hδ hthird
    have hupU : U∉badup := fun hu => hU (Or.inl hu)
    have hloU : U∉badlo := fun hu => hU (Or.inr hu)
    exact ⟨hlower U hloU δ hδ hthird,hupper U hupU δ hδ (by linarith)⟩

end LocalCertification.Protocol
