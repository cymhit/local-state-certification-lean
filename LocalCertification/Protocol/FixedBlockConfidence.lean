import LocalCertification.Protocol.FixedBlockConsumers
import LocalCertification.Protocol.ConfidenceHierarchy

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- Actual physical fixed-block hierarchy for any fixed confidence cutoff below one half. -/
theorem fixedBlock_hierarchy_confidence (k : ℕ) (hk : 1≤k)
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
    qudit_confidence_hierarchy (2^k) (fixedBlock_dimension_ge_two k hk) a b hb hab ha δstar hs0 hshalf
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

/-- A uniform physical logarithmic maximum budget for all errors below the fixed cutoff. -/
def FixedBlockConfidenceLogBound {k : ℕ} (P : (m : ℕ) → FixedBlockPartition k m)
    (good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1))
    (a b δstar : ℝ) : Prop :=
  ∃ C : ℝ,0<C ∧ ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤δstar →
    ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
      ENNReal.ofReal (C*Real.log (1/δ))

/-- Full Corollary6.2: arbitrary fixed delta-star<1/2 and the actual necessary and sufficient
constant-log budget criterion, with the same physical Haar-typical target sequence. -/
theorem fixedBlock_corollary_six_two_confidence (k : ℕ) (hk : 1≤k)
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
    fixedBlock_hierarchy_confidence k hk P a b hb hab ha δstar hs0 hshalf
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

end LocalCertification.Protocol
