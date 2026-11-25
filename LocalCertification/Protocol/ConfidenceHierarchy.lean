import LocalCertification.Protocol.ExponentialHierarchy
import LocalCertification.Protocol.ConfidenceExponentialLower

set_option autoImplicit false
open MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- Degree zero and all critical preceding-degree inequalities share the exponential lower interface. -/
theorem qudit_budget_power_lower_confidence (d r : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (ha : a≤1) (hb0 : 0<b) (hb1 : b<1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2)
    (hg : r=0 ∨ (a-b)/(1-b)≤gamma ((d:ℝ)+1) (r-1)) :
    ∃ c cprob : ℝ,0<c ∧ 0<cprob ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (Real.exp (-cprob*n)) ∧
        ∀ U,U∉bad → ∀ δ : ℝ,0<δ → δ≤δstar →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (haarPureVector ψ₀ U) a b δ := by
  by_cases hr : r=0
  · subst r
    obtain ⟨c,hc,hN⟩ := constant_budget_lower_confidence d hd b hb0 hb1 δstar hs0 hshalf
    refine ⟨c,1,hc,by norm_num,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    refine ⟨∅,MeasurableSet.empty,by simp,?_⟩
    intro U _ δ hδ hcut
    simpa using (hn (haarPureVector ψ₀ U) a ha δ hδ hcut).1
  · have hr' : r-1+1=r := by omega
    have hgap := hg.resolve_left hr
    obtain ⟨c,cprob,C,hc,hcprob,_hC,hN⟩ := exponentialHaar_budget_lower_confidence hd (r-1) b hb0 hb1 δstar hs0 hshalf
    refine ⟨c,cprob,hc,hcprob,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    obtain ⟨hmax,hm,hprob,hbound⟩ := hn ψ₀
    refine ⟨(dualHaarGoodEvent hd (r-1) ψ₀ hmax C (exponentialOverlapCutoff d n))ᶜ,hm.compl,hprob,?_⟩
    intro U hU δ hδ hcut
    have hmem : U∈dualHaarGoodEvent hd (r-1) ψ₀ hmax C (exponentialOverlapCutoff d n) :=
      by simpa only [Set.mem_compl_iff,not_not] using hU
    simpa only [hr'] using (hbound U hmem a δ hgap hδ hcut).1

/-- Actual canonical-sphere compact target sets have an exponentially small complement and retain
both critical budget bounds simultaneously for all delta. All operator and information hypotheses
are discharged by the original Haar/Pauli readout and physical hard-state constructions. -/
theorem qudit_budget_sphere_confidence (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C cprob : ℝ,0<c ∧ 0<C ∧ 0<cprob ∧ ∀ᶠ n : ℕ in atTop,
      ∃ good : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),IsCompact good ∧
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) goodᶜ≤ENNReal.ofReal (Real.exp (-cprob*n)) ∧
        ∀ ψ∈good,∀ δ : ℝ,0<δ → δ≤δstar →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
          expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  have hb1 : b<1 := hab.trans_le ha
  have hq : 1<(d:ℝ)+1 := by
    have : (2:ℝ)≤d := by exact_mod_cast hd
    linarith
  have hg : 0<(a-b)/(1-b) := div_pos (sub_pos.mpr hab) (sub_pos.mpr hb1)
  have hu : gamma ((d:ℝ)+1) r<(a-b)/(1-b) := criticalDegree_spec _ hq _ hg
  have hl : r=0 ∨ (a-b)/(1-b)≤gamma ((d:ℝ)+1) (r-1) := by
    by_cases hr : r=0
    · exact Or.inl hr
    · exact Or.inr (criticalDegree_bracket _ hq _ hg (by omega : 0<r)).2
  obtain ⟨C,cu,hC,hcu,hup⟩ := qudit_budget_upper_exponential d r hd a b ha hb.le hb1 hu
  obtain ⟨c,cl,hc,hcl,hlo⟩ := qudit_budget_power_lower_confidence d r hd a b ha hb hb1 δstar hs0 hshalf hl
  let rate := min cu cl
  have hrate : 0<rate := lt_min hcu hcl
  refine ⟨c,C,rate/2,hc,hC,by positivity,?_⟩
  filter_upwards [hup,hlo,constant_exp_absorb 3 rate hrate] with n hnup hnlo hnabs
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨ψ₀⟩ := NormedSpace.sphere_nonempty_rclike (E:=EuclideanSpace ℂ (QuditIndex d n)) ℂ
    (show (0:ℝ)≤1 by norm_num)
  obtain ⟨badup,hmup,hpup,hupper⟩ := hnup ψ₀
  obtain ⟨badlo,hmlo,hplo,hlower⟩ := hnlo ψ₀
  let e := Real.exp (-rate*n)
  have he : 0<e := Real.exp_pos _
  have hpup' : complexUnitaryHaar (QuditIndex d n) badup≤ENNReal.ofReal e := by
    apply hpup.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hle : rate≤cu := min_le_left _ _
    nlinarith [show (0:ℝ)≤n from Nat.cast_nonneg n]
  have hplo' : complexUnitaryHaar (QuditIndex d n) badlo≤ENNReal.ofReal e := by
    apply hplo.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hle : rate≤cl := min_le_right _ _
    nlinarith [show (0:ℝ)≤n from Nat.cast_nonneg n]
  obtain ⟨good,hcompact,hprob,hfiber⟩ := haar_good_compact_targets (QuditIndex d n) ψ₀
    (badup∪badlo) (hmup.union hmlo) e he
  refine ⟨good,hcompact,?_,?_⟩
  · calc
      _≤complexUnitaryHaar (QuditIndex d n) (badup∪badlo)+ENNReal.ofReal e := hprob
      _≤(ENNReal.ofReal e+ENNReal.ofReal e)+ENNReal.ofReal e :=
        add_le_add ((measure_union_le _ _).trans (add_le_add hpup' hplo')) le_rfl
      _=ENNReal.ofReal (3*e) := by
        rw [← ENNReal.ofReal_add he.le he.le,← ENNReal.ofReal_add (by positivity) he.le]
        congr 1
        ring
      _≤_ := ENNReal.ofReal_le_ofReal hnabs
  · intro ψ hψ δ hδ hcut
    obtain ⟨U,hU,hUψ⟩ := hfiber ψ hψ
    have hupU : U∉badup := fun hu => hU (Or.inl hu)
    have hloU : U∉badlo := fun hu => hU (Or.inr hu)
    have h := And.intro (hlower U hloU δ hδ hcut) (hupper U hupU δ hδ (by linarith))
    simpa only [haarPureVector,hUψ] using h

/-- The exponential hierarchy for any fixed confidence cutoff below one half in the original model. The same global compact target
sequence works for every error level; its exceptional probability is at most exp(-cprob*n). -/
theorem qudit_exponential_confidence_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C cprob : ℝ,0<c ∧ 0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n,IsCompact (good n)) ∧ ∀ᶠ n : ℕ in atTop,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤ENNReal.ofReal (Real.exp (-cprob*n)) ∧
      ∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤δstar →
        ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
        expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  classical
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  obtain ⟨c,C,cprob,hc,hC,hcprob,hN⟩ := qudit_budget_sphere_confidence d hd a b hb hab ha δstar hs0 hshalf
  let P (n : ℕ) (s : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)) : Prop :=
    IsCompact s ∧ canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) sᶜ≤ENNReal.ofReal (Real.exp (-cprob*n)) ∧
    ∀ ψ∈s,∀ δ : ℝ,0<δ → δ≤δstar →
      ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
      expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
      ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ))
  let good (n : ℕ) : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
    if h : ∃ s,P n s then h.choose else ∅
  have hcompact (n : ℕ) : IsCompact (good n) := by
    by_cases h : ∃ s,P n s
    · simpa only [good,dite_eq_left h] using h.choose_spec.1
    · simpa only [good,dite_eq_right h] using isCompact_empty
  refine ⟨c,C,cprob,hc,hC,hcprob,good,hcompact,?_⟩
  filter_upwards [hN] with n hn
  have h : ∃ s,P n s := hn
  have hP : P n (good n) := by simpa only [good,dite_eq_left h] using h.choose_spec
  exact hP.2

/-- The full Theorem1.1 confidence-range extension: any fixed delta-star in (0,1/2), with one
compact canonical target sequence simultaneously controlling all smaller actual errors. -/
theorem qudit_confidence_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C : ℝ,0<c ∧ 0<C ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n,IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
      ∀ᶠ n : ℕ in atTop,∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤δstar →
        ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
        expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤
          ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  obtain ⟨c,C,cprob,hc,hC,hcprob,good,hcompact,hN⟩ :=
    qudit_exponential_confidence_hierarchy d hd a b hb hab ha δstar hs0 hshalf
  have ht : Tendsto (fun n : ℕ => Real.exp (-cprob*n)) atTop (nhds 0) := by
    simpa only [pow_zero,one_mul] using nat_pow_exp_decay cprob hcprob 0
  have hzero : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ)
      atTop (nhds 0) := by
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-cprob*n))) atTop (nhds 0) := by
      simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun _ => bot_le)) (hN.mono (fun _ hn => hn.1))
  have hone : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
      atTop (nhds 1) := by
    have h := (ENNReal.continuous_sub_left (show (1:ℝ≥0∞)≠∞ by simp)).continuousAt.tendsto.comp hzero
    have heq (n : ℕ) : 1-canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ=
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n) := by
      let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
      simpa only [compl_compl] using (prob_compl_eq_one_sub (hcompact n).isClosed.measurableSet.compl).symm
    simpa only [Function.comp_def,tsub_zero,heq] using h
  exact ⟨c,C,hc,hC,good,hcompact,hone,hN.mono (fun _ hn => hn.2)⟩

end LocalCertification.Protocol
