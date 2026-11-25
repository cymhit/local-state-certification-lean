import LocalCertification.Protocol.FixedBlockConsequences

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- A uniform logarithmic maximum budget on the same physical typical target sets. -/
def FixedBlockLogBound {k : ℕ} (P : (m : ℕ) → FixedBlockPartition k m)
    (good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1))
    (a b : ℝ) : Prop :=
  ∃ C : ℝ,0<C ∧ ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤1/3 →
    ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
      ENNReal.ofReal (C*Real.log (1/δ))

/-- Positive degree rules out even a uniform logarithmic expected budget on typical targets.
The proof uses nonempty good sets forced by their actual Haar probability tending to one. -/
theorem fixedBlock_log_obstruction {k : ℕ} (P : (m : ℕ) → FixedBlockPartition k m)
    (good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1))
    (a b c : ℝ) (r : ℕ) (hc : 0<c) (hr : 1≤r)
    (hprob : Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1))
    (hlower : ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,
      ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/(1/3:ℝ)))≤
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b (1/3)) :
    ¬ ∃ C : ℝ,0<C ∧ ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,
      fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b (1/3)≤
        ENNReal.ofReal (C*Real.log (1/(1/3:ℝ))) := by
  rintro ⟨C,_hC,hupper⟩
  have hlim := polynomial_log_budget_diverges r hr c (1/3) hc
    (by norm_num) (by norm_num) (fun m => ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/(1/3:ℝ))))
    (Filter.Eventually.of_forall (fun _ => le_rfl))
  have hgt := hlim.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top :
    ENNReal.ofReal (C*Real.log (1/(1/3:ℝ)))<∞))
  have hne := hprob.eventually (eventually_ne_nhds (one_ne_zero : (1:ℝ≥0∞)≠0))
  obtain ⟨m,hmlo,hmup,hmgt,hmne⟩ := (hlower.and (hupper.and (hgt.and hne))).exists
  have hnonempty : (good m).Nonempty := by
    by_contra hn
    have he : good m=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    exact hmne (by rw [he,measure_empty])
  obtain ⟨ψ,hψ⟩ := hnonempty
  exact (not_le_of_gt hmgt) ((hmlo ψ hψ).trans (hmup ψ hψ))

/-- Actual logarithmic maximum budget is possible exactly above the strict block threshold,
for any common typical sets carrying the proved two-sided polynomial hierarchy. -/
theorem fixedBlock_log_iff {k : ℕ} (hk : 1≤k) (P : (m : ℕ) → FixedBlockPartition k m)
    (a b c C : ℝ) (_hb : 0<b) (hab : b<a) (ha : a≤1) (hc : 0<c)
    (hC : 0<C)
    (good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1))
    (hprob : Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1))
    (hbound : ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤1/3 →
      ENNReal.ofReal (c*(m:ℝ)^criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))*Real.log (1/δ))≤
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
      fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ≤
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
      ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
        ENNReal.ofReal (C*(m:ℝ)^criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))*Real.log (1/δ))) :
    FixedBlockLogBound P good a b ↔ 1/(((2^k:ℕ):ℝ)+1)<(a-b)/(1-b) := by
  have hb1 : b<1 := hab.trans_le ha
  have hg : 0<(a-b)/(1-b) := div_pos (sub_pos.mpr hab) (sub_pos.mpr hb1)
  constructor
  · rintro ⟨Cl,hCl,hlog⟩
    by_contra hn
    have hr := (fixedBlock_degree_positive_iff k hk _ hg).mpr (le_of_not_gt hn)
    apply fixedBlock_log_obstruction P good a b c _ hc hr hprob
    · filter_upwards [hbound] with m hm
      intro ψ hψ
      exact (hm ψ hψ (1/3) (by norm_num) le_rfl).1
    · refine ⟨Cl,hCl,?_⟩
      filter_upwards [hbound,hlog] with m hm hl
      intro ψ hψ
      exact (hm ψ hψ (1/3) (by norm_num) le_rfl).2.1.trans
        (hl ψ hψ (1/3) (by norm_num) le_rfl)
  · intro hg'
    have hz := (fixedBlock_degree_zero_iff k hk _ hg).mpr hg'
    refine ⟨C,hC,?_⟩
    filter_upwards [hbound] with m hm
    intro ψ hψ δ hδ hthird
    simpa only [hz,pow_zero,mul_one] using (hm ψ hψ δ hδ hthird).2.2

/-- For the fixed-block basis model, the necessary and sufficient
constant-logarithmic budget condition on the same Haar-typical compact target sets. -/
theorem fixedBlock_corollary_six_two (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m) (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree (((2^k:ℕ):ℝ)+1) ((a-b)/(1-b))
    ∃ c C : ℝ,0<c ∧ 0<C ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1) ∧
      (∀ᶠ m : ℕ in atTop,∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤1/3 →
        ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ≤
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
          ENNReal.ofReal (C*(m:ℝ)^r*Real.log (1/δ))) ∧
      (FixedBlockLogBound P good a b ↔ 1/(((2^k:ℕ):ℝ)+1)<(a-b)/(1-b)) := by
  dsimp only
  obtain ⟨c,C,hc,hC,good,hcompact,hprob,hbound⟩ := fixedBlock_hierarchy k hk P a b hb hab ha
  exact ⟨c,C,hc,hC,good,hcompact,hprob,hbound,
    fixedBlock_log_iff hk P a b c C hb hab ha hc hC good hprob hbound⟩

/-- In the positive-degree region every target sequence eventually staying in the common good
sets has divergent actual expected budget, and hence divergent maximum budget. -/
theorem fixedBlock_budgets_diverge {k : ℕ} (P : (m : ℕ) → FixedBlockPartition k m)
    (a b c δ : ℝ) (r : ℕ) (hc : 0<c) (hr : 1≤r) (hδ : 0<δ) (hδ1 : δ<1)
    (ψ : (m : ℕ) → QIT.PureVector (QuditIndex 2 (k*m)))
    (hbound : ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤fixedBlockExpectedBudget (P m) (ψ m) a b δ ∧
      fixedBlockExpectedBudget (P m) (ψ m) a b δ≤ENat.toENNReal (fixedBlockMaximumBudget (P m) (ψ m) a b δ)) :
    Tendsto (fun m => fixedBlockExpectedBudget (P m) (ψ m) a b δ) atTop (nhds ∞) ∧
    Tendsto (fun m => ENat.toENNReal (fixedBlockMaximumBudget (P m) (ψ m) a b δ)) atTop (nhds ∞) := by
  constructor
  · apply polynomial_log_budget_diverges r hr c δ hc hδ hδ1
    exact hbound.mono (fun _ h => h.1)
  · apply polynomial_log_budget_diverges r hr c δ hc hδ hδ1
    exact hbound.mono (fun _ h => h.1.trans h.2)

end LocalCertification.Protocol
