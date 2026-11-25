import LocalCertification.Protocol.ConfidenceHierarchy

set_option autoImplicit false
open MeasureTheory InformationTheory Filter Metric LocalCertification.Information LocalCertification.Quantum LocalCertification.Extremal CertificationGaussian
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The exact terminal testing scale is retained before any confidence cutoff is selected.
The dimension threshold and the denominator state depend on b, not on delta. -/
theorem constant_budget_testing_scale (d : ℕ) (hd : 2≤d) [NeZero d]
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : QIT.PureVector (QuditIndex d n),∀ a : ℝ,a≤1 →
      ∀ δ : ℝ,0<δ → δ<1/2 →
        ENNReal.ofReal (c*testingThreshold δ)≤expectedBudget ψ a b δ := by
  have hL : 0<4/b+2 := by positivity
  have hd' : (1:ℝ)<d := by exact_mod_cast (show 1<d by omega)
  have ht : Tendsto (fun n : ℕ => ((d:ℝ)^n)⁻¹) atTop (nhds 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0:ℝ)≤(d:ℝ)⁻¹ by positivity) (inv_lt_one_of_one_lt₀ hd')
  refine ⟨(4/b+2)⁻¹,by positivity,?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<b/2 by positivity))] with n hn
  intro ψ a ha δ hδ hhalf
  apply expectedBudget_lower
  intro Q hv
  have hi := valid_information_high_low Q.toRaw ψ a b δ hv hδ hhalf
    ψ.state (constantLowState ψ b hb0 hb1) (by rwa [pureTargetFidelity_self])
    (constantLowState_promised ψ b hb0 hb1 hn.le) (ENNReal.ofReal (4/b+2))
    (constantLowState_klDiv ψ b hb0 hb1)
  have hdv := (ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr hL)) ENNReal.ofReal_ne_top).mpr hi
  rw [← ENNReal.ofReal_div_of_pos hL] at hdv
  have he : ENNReal.ofReal ((4/b+2)⁻¹*testingThreshold δ)≤expectedCopies Q.toRaw ψ.state := by
    simpa only [div_eq_mul_inv,mul_comm] using hdv
  exact he.trans (expectedCopies_le_protocolCost Q.toRaw ψ a b ψ.state
    (Or.inl (by rwa [pureTargetFidelity_self])))

/-- The physical calibrated hard pair supplies all testing errors on one event and one threshold.
Only the displayed scalar testingThreshold depends on delta. -/
theorem exponentialHaar_budget_testing_scale {d : ℕ} [NeZero d] (hd : 2≤d) (r : ℕ)
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) :
    ∃ clower cprob C : ℝ,0<clower ∧ 0<cprob ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ hN : (quditDualCertificate hd r).maxNode≤n,
      MeasurableSet (dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n)) ∧
      complexUnitaryHaar (QuditIndex d n)
        (dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n))ᶜ≤
          ENNReal.ofReal (Real.exp (-cprob*n)) ∧
      ∀ W∈dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n),
        ∀ a δ : ℝ,(a-b)/(1-b)≤gamma ((d:ℝ)+1) r → 0<δ → δ<1/2 →
          ENNReal.ofReal (clower*(n:ℝ)^(r+1)*testingThreshold δ)≤
            expectedBudget (haarPureVector ψ₀ W) a b δ := by
  obtain ⟨c,C,K,hc,hC,hK,hgood⟩ := exponentialHaar_hard_states hd r b hb0 hb1
  have hlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  refine ⟨K⁻¹,min (Real.log (d:ℝ)/4) c/2,C,by positivity,by positivity,hC,?_⟩
  filter_upwards [hgood,eventually_ge_atTop 1,
    exponential_failure_absorb ((r+1:ℕ):ℝ) (Real.log (d:ℝ)/4) c (by positivity) (by positivity) hc]
    with n hn hn1 hfail
  intro ψ₀
  obtain ⟨hN,hm,hprob,hpair⟩ := hn ψ₀
  refine ⟨hN,hm,?_,?_⟩
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hprob
    exact hprob.trans (ENNReal.ofReal_le_ofReal hfail)
  · intro W hW a δ hgap hδ hhalf
    obtain ⟨hlb,_hlo,_hhi,hL⟩ := hpair W hW
    have hp := calibratedNumerator_promised hd r (haarPureVector ψ₀ W) hN a b hb0 hb1 hlb hgap
    apply expectedBudget_lower
    intro Q hv
    have hraw := expected_cost_power_lower K (testingThreshold δ) hK n r hn1 _
      (calibrated_terminal_information hd r _ hN a b δ hb0 hb1 hlb hgap hδ hhalf Q.toRaw hv _ hL)
    have he : ENNReal.ofReal (K⁻¹*(n:ℝ)^(r+1)*testingThreshold δ)≤
        expectedCopies Q.toRaw (calibratedNumeratorState hd r (haarPureVector ψ₀ W) hN b hb0 hb1 hlb) := by
      simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hraw
    exact he.trans (expectedCopies_le_protocolCost Q.toRaw (haarPureVector ψ₀ W) a b _ hp)

/-- Every critical degree, including zero, has a delta-independent good event and size threshold. -/
theorem qudit_budget_power_testing_scale (d r : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (ha : a≤1) (hb0 : 0<b) (hb1 : b<1)
    (hg : r=0 ∨ (a-b)/(1-b)≤gamma ((d:ℝ)+1) (r-1)) :
    ∃ c cprob : ℝ,0<c ∧ 0<cprob ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (Real.exp (-cprob*n)) ∧
        ∀ U,U∉bad → ∀ δ : ℝ,0<δ → δ<1/2 →
          ENNReal.ofReal (c*(n:ℝ)^r*testingThreshold δ)≤expectedBudget (haarPureVector ψ₀ U) a b δ := by
  by_cases hr : r=0
  · subst r
    obtain ⟨c,hc,hN⟩ := constant_budget_testing_scale d hd b hb0 hb1
    refine ⟨c,1,hc,by norm_num,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    refine ⟨∅,MeasurableSet.empty,by simp,?_⟩
    intro U _ δ hδ hhalf
    simpa using hn (haarPureVector ψ₀ U) a ha δ hδ hhalf
  · have hr' : r-1+1=r := by omega
    obtain ⟨c,cprob,C,hc,hcprob,_hC,hN⟩ := exponentialHaar_budget_testing_scale hd (r-1) b hb0 hb1
    refine ⟨c,cprob,hc,hcprob,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    obtain ⟨hmax,hm,hprob,hbound⟩ := hn ψ₀
    refine ⟨(dualHaarGoodEvent hd (r-1) ψ₀ hmax C (exponentialOverlapCutoff d n))ᶜ,hm.compl,hprob,?_⟩
    intro U hU δ hδ hhalf
    have hmem : U∈dualHaarGoodEvent hd (r-1) ψ₀ hmax C (exponentialOverlapCutoff d n) :=
      by simpa only [Set.mem_compl_iff,not_not] using hU
    simpa only [hr'] using hbound U hmem a δ (hg.resolve_left hr) hδ hhalf

end LocalCertification.Protocol
