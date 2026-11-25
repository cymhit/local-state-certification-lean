import LocalCertification.Protocol.MeasurableBudgetHierarchy
import LocalCertification.Protocol.MeasurableFixedBlockBudgets
import LocalCertification.Protocol.FixedBlockConsequences

/-! Fixed prescribed partitions with arbitrary measurable POVMs inside each
block. The actual execution-law and optimized-budget equalities transport the
general product theorem. The partition is fixed across all copies; the target
family and size cutoff precede every confidence cutoff. Coordinate transport
and the scalar degree and divergence criteria preserve physical copy costs. -/

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian LocalCertification.Asymptotic
  LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.FixedBlock
universe u

/-- Exact testing-scale hierarchy on physical qubit targets for any prescribed partition. -/
theorem fixedBlock_budget_sphere_hierarchy (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m)
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))
    ∃ c C cprob : ℝ, 0<c ∧ 0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*n))) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*n))) (good n)) atTop (nhds 1) ∧
    ∃ N : ℕ, 1≤N ∧ ∀ n, N≤n →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*n))) (good n)ᶜ ≤
        ENNReal.ofReal (Real.exp (-cprob*n)) ∧
      ∀ ψ∈good n, ∀ δ : ℝ, 0<δ → δ<1/2 →
        ENNReal.ofReal (c*(n:ℝ)^r*testingThreshold δ) ≤ expectedBudget.{u} (P n) (spherePureVector ψ) a b δ ∧
        expectedBudget.{u} (P n) (spherePureVector ψ) a b δ ≤ ENat.toENNReal (maximumBudget.{u} (P n) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget.{u} (P n) (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  obtain ⟨c,C,cprob,hc,hC,hcprob,good,hcompact,hprob,N,hNpos,hN⟩ :=
    ProductBudget.product_budget_sphere_hierarchy.{u} (2^k)
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
  refine ⟨c,C,cprob,hc,hC,hcprob,physicalGood,hphys,?_,N,hNpos,?_⟩
  · have heq (m : ℕ) := hmeasure m (good m) (hcompact m).isClosed.measurableSet
    simpa only [physicalGood,heq] using hprob
  · intro m hm
    refine ⟨?_,?_⟩
    · change canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m)))
        ((fixedBlockSphere (P m)) ⁻¹' (good m)ᶜ)≤_
      rw [hmeasure m (good m)ᶜ (hcompact m).isClosed.measurableSet.compl]
      exact (hN m hm).1
    · intro ψ hψ δ hδ hhalf
      rw [expectedBudget_eq,maximumBudget_eq,←fixedBlockSphere_pure]
      exact (hN m hm).2 (fixedBlockSphere (P m) ψ) hψ δ hδ hhalf

/-- The same exponentially typical target family and dimension cutoff work for all fixed confidence cutoffs. -/
theorem fixedBlock_budget_same_event_confidence_hierarchy (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m) (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree (((2^k : ℕ) : ℝ)+1) ((a-b)/(1-b))
    ∃ C cprob : ℝ,0<C ∧ 0<cprob ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1) ∧
    ∃ N : ℕ, 1≤N ∧
      (∀ m,N≤m → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)ᶜ≤
        ENNReal.ofReal (Real.exp (-cprob*m))) ∧
      ∀ δstar : ℝ,0<δstar → δstar<1/2 → ∃ c : ℝ,0<c ∧
        ∀ m,N≤m → ∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤δstar →
          ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤expectedBudget.{u} (P m) (spherePureVector ψ) a b δ ∧
          expectedBudget.{u} (P m) (spherePureVector ψ) a b δ≤
            ENat.toENNReal (maximumBudget.{u} (P m) (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget.{u} (P m) (spherePureVector ψ) a b δ)≤
            ENNReal.ofReal (C*(m:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  let r := criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))
  obtain ⟨A,C,cprob,hA,hC,hcprob,good,hcompact,hone,N,hNpos,hN⟩ :=
    fixedBlock_budget_sphere_hierarchy.{u} k hk P a b hb hab ha
  refine ⟨C,cprob,hC,hcprob,good,hcompact,hone,N,hNpos,fun n hn => (hN n hn).1,?_⟩
  intro δstar hs0 hshalf
  obtain ⟨k, hk, hcompare⟩ := testingThreshold_confidence_lower_via_continuous_ratio δstar hs0 hshalf
  refine ⟨A*k, mul_pos hA hk, ?_⟩
  intro n hn ψ hψ δ hδ hcut
  obtain ⟨hlo,hmid,hup⟩ := (hN n hn).2 ψ hψ δ hδ (hcut.trans_lt hshalf)
  refine ⟨?_,hmid,hup⟩
  apply (ENNReal.ofReal_le_ofReal ?_).trans hlo
  have h := mul_le_mul_of_nonneg_left
    (hcompare δ hδ hcut)
    (show (0:ℝ)≤A*(n:ℝ)^r by positivity)
  convert h using 1
  ring

/-- On that same family, constant-log budgets hold exactly above the strict zero-degree threshold; both budgets diverge at or below it. -/
theorem fixedBlock_budget_same_event_criterion (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m) (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree (((2^k : ℕ) : ℝ)+1) ((a-b)/(1-b))
    ∃ C cprob : ℝ,0<C ∧ 0<cprob ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1) ∧
    ∃ N : ℕ, 1≤N ∧
      (∀ m,N≤m → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)ᶜ≤
        ENNReal.ofReal (Real.exp (-cprob*m))) ∧
      (∀ δstar : ℝ,0<δstar → δstar<1/2 → ∃ c : ℝ,0<c ∧
        ∀ m,N≤m → ∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤δstar →
          ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤expectedBudget.{u} (P m) (spherePureVector ψ) a b δ ∧
          expectedBudget.{u} (P m) (spherePureVector ψ) a b δ≤
            ENat.toENNReal (maximumBudget.{u} (P m) (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget.{u} (P m) (spherePureVector ψ) a b δ)≤
            ENNReal.ofReal (C*(m:ℝ)^r*Real.log (1/δ))) ∧
      (∀ δstar : ℝ,0<δstar → δstar<1/2 →
        ((∃ Cl : ℝ, 0<Cl ∧ ∀ᶠ m : ℕ in atTop, ∀ ψ∈good m, ∀ δ : ℝ, 0<δ → δ≤δstar →
          ENat.toENNReal (maximumBudget.{u} (P m) (spherePureVector ψ) a b δ)≤ENNReal.ofReal (Cl*Real.log (1/δ))) ↔ 1/(((2^k:ℕ):ℝ)+1)<(a-b)/(1-b))) ∧
      ((a-b)/(1-b)≤1/(((2^k:ℕ):ℝ)+1) → ∀ δ : ℝ,0<δ → δ<1/2 →
        ∀ B : ℝ≥0∞,B<∞ → ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,
          B<expectedBudget.{u} (P m) (spherePureVector ψ) a b δ ∧
          B<ENat.toENNReal (maximumBudget.{u} (P m) (spherePureVector ψ) a b δ)) := by
  dsimp only
  obtain ⟨C,cprob,hC,hcprob,good,hcompact,hprob,N,hNpos,hbad,hcut⟩ :=
    fixedBlock_budget_same_event_confidence_hierarchy.{u} k hk P a b hb hab ha
  have hg : 0<(a-b)/(1-b) := div_pos (sub_pos.mpr hab) (sub_pos.mpr (hab.trans_le ha))
  let r := criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))
  have hdiv : (a-b)/(1-b)≤1/(((2^k:ℕ):ℝ)+1) → ∀ δ : ℝ,0<δ → δ<1/2 →
      ∀ B : ℝ≥0∞,B<∞ → ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,
        B<expectedBudget.{u} (P m) (spherePureVector ψ) a b δ ∧
        B<ENat.toENNReal (maximumBudget.{u} (P m) (spherePureVector ψ) a b δ) := by
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
  refine ⟨C,cprob,hC,hcprob,good,hcompact,hprob,N,hNpos,hbad,hcut,?_,hdiv⟩
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

end LocalCertification.Protocol.MeasurableExecution.FixedBlock
