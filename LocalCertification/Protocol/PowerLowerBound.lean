import LocalCertification.Protocol.ConstantLowerBound

set_option autoImplicit false
open MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The zero and positive degrees share one lower-bound interface. At positive degree the preceding
critical value is included; at zero degree a genuine all-target hard pair supplies the logarithm. -/
theorem qudit_budget_power_lower (d r : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (ha : a≤1) (hb0 : 0<b) (hb1 : b<1)
    (hg : r=0 ∨ (a-b)/(1-b)≤gamma ((d:ℝ)+1) (r-1)) :
    ∃ c cdecay : ℝ,0<c ∧ 0<cdecay ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤
          ENNReal.ofReal ((r:ℝ)/(n:ℝ)^3)+ENNReal.ofReal (Real.exp (-cdecay*(n:ℝ)^3)) ∧
        ∀ U,U∉bad → ∀ δ : ℝ,0<δ → δ≤1/3 →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤
            expectedBudget (haarPureVector ψ₀ U) a b δ := by
  by_cases hr : r=0
  · subst r
    obtain ⟨c,hc,hN⟩ := constant_budget_lower_eventually d hd b hb0 hb1
    refine ⟨c,1,hc,by norm_num,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    refine ⟨∅,MeasurableSet.empty,by simp,?_⟩
    intro U _ δ hδ hthird
    simpa using (hn (haarPureVector ψ₀ U) a ha δ hδ hthird).1
  · have hr' : r-1+1=r := by omega
    have hgap : (a-b)/(1-b)≤gamma ((d:ℝ)+1) (r-1) := hg.resolve_left hr
    obtain ⟨cdecay,C,K,hdecay,_hC,hK,N,hN⟩ := calibratedHaar_budget_lower hd (r-1) b hb0 hb1
    refine ⟨1/(6*K),cdecay,by positivity,hdecay,?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    intro ψ₀
    obtain ⟨hmax,hm,hprob,hbound⟩ := hN n hn ψ₀
    refine ⟨(dualHaarGoodEvent hd (r-1) ψ₀ hmax C (dualOverlapCutoff d n))ᶜ,
      hm.compl,?_,?_⟩
    · simpa only [hr'] using hprob
    · intro U hU δ hδ hthird
      have hmem : U∈dualHaarGoodEvent hd (r-1) ψ₀ hmax C (dualOverlapCutoff d n) :=
        by simpa only [Set.mem_compl_iff, not_not] using hU
      have h := (hbound U hmem a δ hgap hδ (by linarith)).1
      rw [hr'] at h
      apply (ENNReal.ofReal_le_ofReal ?_).trans h
      have ht := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (testingThreshold_log_lower δ hδ hthird) hK.le)
        (show (0:ℝ)≤(n:ℝ)^r by positivity)
      convert ht using 1
      field_simp

end LocalCertification.Protocol
