import LocalCertification.Protocol.SameConfidenceEvent

set_option autoImplicit false
open MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The target family and size threshold work for every fixed error in (0, 1/2).
Only the comparison constants absorb the logarithmic confidence factor. -/
theorem qudit_same_event_fixed_error_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ cprob : ℝ,0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n,IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
    ∃ N : ℕ,
      (∀ n,N≤n → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤
        ENNReal.ofReal (Real.exp (-cprob*n))) ∧
      ∀ δ : ℝ,0<δ → δ<1/2 → ∃ c C : ℝ,0<c ∧ 0<C ∧
        ∀ n,N≤n → ∀ ψ∈good n,
          ENNReal.ofReal (c*(n:ℝ)^r)≤expectedBudget (spherePureVector ψ) a b δ ∧
          expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤ENNReal.ofReal (C*(n:ℝ)^r) := by
  dsimp only
  obtain ⟨C,cprob,hC,hcprob,good,hcompact,hone,N,hprob,hall⟩ :=
    qudit_same_event_confidence_hierarchy d hd a b hb hab ha
  refine ⟨cprob,hcprob,good,hcompact,hone,N,hprob,?_⟩
  intro δ hδ hhalf
  obtain ⟨c,hc,hbound⟩ := hall δ hδ hhalf
  have hlog : 0<Real.log (1/δ) := Real.log_pos ((one_lt_div hδ).mpr (by linarith))
  refine ⟨c*Real.log (1/δ),C*Real.log (1/δ),mul_pos hc hlog,mul_pos hC hlog,?_⟩
  intro n hn ψ hψ
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound n hn ψ hψ δ hδ le_rfl

/-- The one-third bound and every fixed cutoff below one half share the target family and size threshold. -/
theorem qudit_same_event_all_confidence_ranges (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ C cprob : ℝ,0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n,IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
    ∃ N : ℕ,
      (∀ n,N≤n → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤
        ENNReal.ofReal (Real.exp (-cprob*n))) ∧
      (∃ c : ℝ,0<c ∧ ∀ n,N≤n → ∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤1/3 →
        ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
        expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ))) ∧
      (∀ δstar : ℝ,0<δstar → δstar<1/2 → ∃ c : ℝ,0<c ∧
        ∀ n,N≤n → ∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤δstar →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
          expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ))) ∧
      ∀ δ : ℝ,0<δ → δ<1/2 → ∃ cδ Cδ : ℝ,0<cδ ∧ 0<Cδ ∧
        ∀ n,N≤n → ∀ ψ∈good n,
          ENNReal.ofReal (cδ*(n:ℝ)^r)≤expectedBudget (spherePureVector ψ) a b δ ∧
          expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤ENNReal.ofReal (Cδ*(n:ℝ)^r) := by
  dsimp only
  obtain ⟨C,cprob,hC,hcprob,good,hcompact,hone,N,hprob,hall⟩ :=
    qudit_same_event_confidence_hierarchy d hd a b hb hab ha
  refine ⟨C,cprob,hC,hcprob,good,hcompact,hone,N,hprob,
    hall (1/3) (by norm_num) (by norm_num),hall,?_⟩
  intro δ hδ hhalf
  obtain ⟨c,hc,hbound⟩ := hall δ hδ hhalf
  have hlog : 0<Real.log (1/δ) := Real.log_pos ((one_lt_div hδ).mpr (by linarith))
  refine ⟨c*Real.log (1/δ),C*Real.log (1/δ),mul_pos hc hlog,mul_pos hC hlog,?_⟩
  intro n hn ψ hψ
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound n hn ψ hψ δ hδ le_rfl

end LocalCertification.Protocol
