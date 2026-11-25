import LocalCertification.Protocol.FixedBlockConsumers
import LocalCertification.Protocol.FixedBlockConfidence
import LocalCertification.Protocol.UniformConfidenceHierarchy

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- A common physical target family, exponential exceptional probability and size threshold
are fixed before the confidence cutoff. Costs count copies of the entire qubit state. -/
theorem fixedBlock_same_event_continuous_confidence_hierarchy (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m) (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree (((2^k : ℕ) : ℝ)+1) ((a-b)/(1-b))
    ∃ C cprob : ℝ,0<C ∧ 0<cprob ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1) ∧
    ∃ N : ℕ,
      (∀ m,N≤m → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)ᶜ≤
        ENNReal.ofReal (Real.exp (-cprob*m))) ∧
      ∀ δstar : ℝ,0<δstar → δstar<1/2 → ∃ c : ℝ,0<c ∧
        ∀ m,N≤m → ∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤δstar →
          ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
          fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ≤
            ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
            ENNReal.ofReal (C*(m:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  obtain ⟨C,cprob,hC,hcprob,good,hcompact,hprob,N,hbad,hcut⟩ :=
    qudit_same_event_continuous_confidence_hierarchy (2^k)
      (fixedBlock_dimension_ge_two k hk) a b hb hab ha
  let physicalGood (m : ℕ) := (fixedBlockSphere (P m)) ⁻¹' good m
  have hphys (m : ℕ) : IsCompact (physicalGood m) :=
    (fixedBlockSphere (P m)).isCompact_preimage.mpr (hcompact m)
  have hmeasure (m : ℕ) (s : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex (2^k) m)) 1))
      (hs : MeasurableSet s) :
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) ((fixedBlockSphere (P m)) ⁻¹' s)=
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex (2^k) m)) s := by
    have h := congrArg (fun μ : Measure (sphere (0 : EuclideanSpace ℂ (QuditIndex (2^k) m)) 1) => μ s)
      (fixedBlockSphere_measure (P m))
    rw [Measure.map_apply (fixedBlockSphere (P m)).measurable hs] at h
    exact h
  refine ⟨C,cprob,hC,hcprob,physicalGood,hphys,?_,N,?_,?_⟩
  · have heq (m : ℕ) := hmeasure m (good m) (hcompact m).isClosed.measurableSet
    simpa only [physicalGood,heq] using hprob
  · intro m hm
    change canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m)))
      ((fixedBlockSphere (P m)) ⁻¹' (good m)ᶜ)≤_
    rw [hmeasure m (good m)ᶜ (hcompact m).isClosed.measurableSet.compl]
    exact hbad m hm
  · intro δstar hs0 hshalf
    obtain ⟨c,hc,hbound⟩ := hcut δstar hs0 hshalf
    refine ⟨c,hc,?_⟩
    intro m hm ψ hψ δ hδ hδcut
    rw [fixedBlockExpectedBudget_eq,fixedBlockMaximumBudget_eq,←fixedBlockSphere_pure]
    exact hbound m hm (fixedBlockSphere (P m) ψ) hψ δ hδ hδcut

/-- Actual physical fixed-block hierarchy for any fixed confidence cutoff below one half. -/
theorem fixedBlock_hierarchy_continuous_confidence (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m) (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2) :
    let r := criticalDegree (((2^k : ℕ) : ℝ)+1) ((a-b)/(1-b))
    ∃ c C : ℝ,0<c ∧ 0<C ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1) ∧
      ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤δstar →
        ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ≤
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
          ENNReal.ofReal (C*(m:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  obtain ⟨c,C,hc,hC,good,hcompact,hprob,hN⟩ :=
    qudit_continuous_confidence_hierarchy (2^k) (fixedBlock_dimension_ge_two k hk) a b hb hab ha δstar hs0 hshalf
  let physicalGood (m : ℕ) := (fixedBlockSphere (P m)) ⁻¹' good m
  have hphys (m : ℕ) : IsCompact (physicalGood m) :=
    (fixedBlockSphere (P m)).isCompact_preimage.mpr (hcompact m)
  have hmeasure (m : ℕ) : canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (physicalGood m)=
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex (2^k) m)) (good m) := by
    have h := congrArg (fun μ : Measure (sphere (0 : EuclideanSpace ℂ (QuditIndex (2^k) m)) 1) => μ (good m))
      (fixedBlockSphere_measure (P m))
    rw [Measure.map_apply (fixedBlockSphere (P m)).measurable (hcompact m).isClosed.measurableSet] at h
    exact h
  refine ⟨c,C,hc,hC,physicalGood,hphys,?_,?_⟩
  · simpa only [hmeasure] using hprob
  · filter_upwards [hN] with m hm
    intro ψ hψ δ hδ hthird
    rw [fixedBlockExpectedBudget_eq,fixedBlockMaximumBudget_eq,←fixedBlockSphere_pure]
    exact hm (fixedBlockSphere (P m) ψ) hψ δ hδ hthird

/-- Full Corollary6.2: arbitrary fixed delta-star<1/2 and the actual necessary and sufficient
constant-log budget criterion, with the same physical Haar-typical target sequence. -/
theorem fixedBlock_log_budget_criterion_continuous_confidence (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m) (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2) :
    let r := criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))
    ∃ c C : ℝ,0<c ∧ 0<C ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1) ∧
      (∀ᶠ m : ℕ in atTop,∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤δstar →
        ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ≤
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
          ENNReal.ofReal (C*(m:ℝ)^r*Real.log (1/δ))) ∧
      (FixedBlockConfidenceLogBound P good a b δstar ↔ 1/(((2^k:ℕ):ℝ)+1)<(a-b)/(1-b)) := by
  dsimp only
  obtain ⟨c,C,hc,hC,good,hcompact,hprob,hbound⟩ :=
    fixedBlock_hierarchy_continuous_confidence k hk P a b hb hab ha δstar hs0 hshalf
  refine ⟨c,C,hc,hC,good,hcompact,hprob,hbound,?_⟩
  have hg : 0<(a-b)/(1-b) := div_pos (sub_pos.mpr hab) (sub_pos.mpr (hab.trans_le ha))
  constructor
  · rintro ⟨Cl,_hCl,hlog⟩
    by_contra hn
    have hr := (fixedBlock_degree_positive_iff k hk _ hg).mpr (le_of_not_gt hn)
    let r := criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))
    have hlim := polynomial_log_budget_diverges r hr c δstar hc hs0 (by linarith)
      (fun m => ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δstar)))
      (Filter.Eventually.of_forall (fun _ => le_rfl))
    have hgt := hlim.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top :
      ENNReal.ofReal (Cl*Real.log (1/δstar))<∞))
    have hne := hprob.eventually (eventually_ne_nhds (one_ne_zero : (1:ℝ≥0∞)≠0))
    obtain ⟨m,hmb,hmup,hmgt,hmne⟩ := (hbound.and (hlog.and (hgt.and hne))).exists
    have hnonempty : (good m).Nonempty := by
      by_contra hn
      have he : good m=∅ := Set.not_nonempty_iff_eq_empty.mp hn
      exact hmne (by rw [he,measure_empty])
    obtain ⟨ψ,hψ⟩ := hnonempty
    have h := hmb ψ hψ δstar hs0 le_rfl
    exact (not_le_of_gt hmgt) (h.1.trans (h.2.1.trans (hmup ψ hψ δstar hs0 le_rfl)))
  · intro hgt
    have hz := (fixedBlock_degree_zero_iff k hk _ hg).mpr hgt
    refine ⟨C,hC,?_⟩
    filter_upwards [hbound] with m hm
    intro ψ hψ δ hδ hcut
    simpa only [hz,pow_zero,mul_one] using (hm ψ hψ δ hδ hcut).2.2

/-- The strict logarithmic-budget criterion and fixed-error divergence hold on the
same physical target family as the common-cutoff hierarchy. -/
theorem fixedBlock_same_event_continuous_confidence_criterion (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m) (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree (((2^k : ℕ) : ℝ)+1) ((a-b)/(1-b))
    ∃ C cprob : ℝ,0<C ∧ 0<cprob ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1) ∧
    ∃ N : ℕ,
      (∀ m,N≤m → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)ᶜ≤
        ENNReal.ofReal (Real.exp (-cprob*m))) ∧
      (∀ δstar : ℝ,0<δstar → δstar<1/2 → ∃ c : ℝ,0<c ∧
        ∀ m,N≤m → ∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤δstar →
          ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
          fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ≤
            ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
            ENNReal.ofReal (C*(m:ℝ)^r*Real.log (1/δ))) ∧
      (∀ δstar : ℝ,0<δstar → δstar<1/2 →
        (FixedBlockConfidenceLogBound P good a b δstar ↔ 1/(((2^k:ℕ):ℝ)+1)<(a-b)/(1-b))) ∧
      ((a-b)/(1-b)≤1/(((2^k:ℕ):ℝ)+1) → ∀ δ : ℝ,0<δ → δ<1/2 →
        ∀ B : ℝ≥0∞,B<∞ → ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,
          B<fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
          B<ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)) := by
  dsimp only
  obtain ⟨C,cprob,hC,hcprob,good,hcompact,hprob,N,hbad,hcut⟩ :=
    fixedBlock_same_event_continuous_confidence_hierarchy k hk P a b hb hab ha
  have hg : 0<(a-b)/(1-b) := div_pos (sub_pos.mpr hab) (sub_pos.mpr (hab.trans_le ha))
  let r := criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))
  have hdiv : (a-b)/(1-b)≤1/(((2^k:ℕ):ℝ)+1) → ∀ δ : ℝ,0<δ → δ<1/2 →
      ∀ B : ℝ≥0∞,B<∞ → ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,
        B<fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        B<ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) := by
    intro hgap δ hδ hhalf B hB
    have hr : 1≤r := (fixedBlock_degree_positive_iff k hk _ hg).mpr hgap
    obtain ⟨c,hc,hbound⟩ := hcut δ hδ hhalf
    have hlim := polynomial_log_budget_diverges r hr c δ hc hδ (by linarith)
      (fun m => ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ)))
      (Filter.Eventually.of_forall (fun _ => le_rfl))
    have hgt := hlim.eventually (lt_mem_nhds hB)
    filter_upwards [eventually_atTop.mpr ⟨N,hbound⟩,hgt] with m hm hlarge
    intro ψ hψ
    have hbnd := hm ψ hψ δ hδ le_rfl
    exact ⟨hlarge.trans_le hbnd.1,hlarge.trans_le (hbnd.1.trans hbnd.2.1)⟩
  refine ⟨C,cprob,hC,hcprob,good,hcompact,hprob,N,hbad,hcut,?_,hdiv⟩
  intro δstar hs0 hshalf
  constructor
  · rintro ⟨Cl,_hCl,hlog⟩
    by_contra hn
    have hlarge := hdiv (le_of_not_gt hn) δstar hs0 hshalf
      (ENNReal.ofReal (Cl*Real.log (1/δstar))) ENNReal.ofReal_lt_top
    have hne := hprob.eventually (eventually_ne_nhds (one_ne_zero : (1:ℝ≥0∞)≠0))
    obtain ⟨m,hmup,hmgt,hmne⟩ := (hlog.and (hlarge.and hne)).exists
    have hnonempty : (good m).Nonempty := by
      by_contra hn
      have he : good m=∅ := Set.not_nonempty_iff_eq_empty.mp hn
      exact hmne (by rw [he,measure_empty])
    obtain ⟨ψ,hψ⟩ := hnonempty
    exact (not_le_of_gt (hmgt ψ hψ).2) (hmup ψ hψ δstar hs0 le_rfl)
  · intro hgt
    have hz := (fixedBlock_degree_zero_iff k hk _ hg).mpr hgt
    obtain ⟨c,_hc,hbound⟩ := hcut δstar hs0 hshalf
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_atTop.mpr ⟨N,hbound⟩] with m hm
    intro ψ hψ δ hδ hδcut
    simpa only [hz,pow_zero,mul_one] using (hm ψ hψ δ hδ hδcut).2.2

end LocalCertification.Protocol
