import LocalCertification.Paper
import LocalCertification.Protocol.MeasurableBudgetHierarchy
import LocalCertification.Protocol.MeasurablePowerLowerBound
import LocalCertification.Protocol.MeasurableProductUpper
import LocalCertification.Protocol.SameConfidenceEvent
import LocalCertification.Information.ConfidenceRange

open MeasureTheory Filter Metric CertificationGaussian LocalCertification.Information
  LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u
example (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C cprob : ℝ, 0<c ∧ 0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
    ∃ N : ℕ, 1≤N ∧ ∀ n, N≤n →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (Real.exp (-cprob*n)) ∧
      ∀ ψ∈good n, ∀ δ : ℝ, 0<δ → δ<1/2 →
        ENNReal.ofReal (c*(n:ℝ)^r*testingThreshold δ) ≤ expectedBudget.{u} (spherePureVector ψ) a b δ ∧
        expectedBudget.{u} (spherePureVector ψ) a b δ ≤ ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) :=
  LocalCertification.Paper.tolerance_testing_bounds d hd a b hb hab ha

example (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ C cprob : ℝ, 0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
    ∃ N : ℕ, 1≤N ∧
      (∀ n, N≤n → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (Real.exp (-cprob*n))) ∧
      ∀ δstar : ℝ, 0<δstar → δstar<1/2 → ∃ c : ℝ, 0<c ∧
        ∀ n, N≤n → ∀ ψ∈good n, ∀ δ : ℝ, 0<δ → δ≤δstar →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ)) ≤ expectedBudget.{u} (spherePureVector ψ) a b δ ∧
          expectedBudget.{u} (spherePureVector ψ) a b δ ≤ ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
            ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) :=
  LocalCertification.Paper.theorem_1 d hd a b hb hab ha
/-- In the live-history model, select the typical family and the upper
constant before the confidence cutoff. The exponent is the first strict
crossing of the manuscript's dimension-indexed step points. -/
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (a b : ℝ)
    (hb : 0 < b) (hab : b < a) (ha : a ≤ 1) :
    let r : ℕ := sInf {j : ℕ | LocalCertification.Manuscript.gamma d j < (a-b)/(1-b)}
    ∃ G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (G n))
        atTop (𝓝 1) ∧ ∃ H : ℝ, 0 < H ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ δstar : ℝ, 0 < δstar → δstar < 1/2 → ∃ L : ℝ, 0 < L ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δstar → ∀ n ≥ N, ∀ ψ ∈ G n,
        ENNReal.ofReal (L * (n:ℝ)^r * Real.log (1/δ)) ≤
          PaperHistoryBudget.expectedBudget.{u} (spherePureVector ψ) a b δ ∧
        PaperHistoryBudget.expectedBudget.{u} (spherePureVector ψ) a b δ ≤
          ENat.toENNReal (PaperHistoryBudget.maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (PaperHistoryBudget.maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (H * (n:ℝ)^r * Real.log (1/δ)) := by
  obtain ⟨H, _, hH, _, G, _, hG, N, hN, _, hc⟩ :=
    LocalCertification.Paper.theorem_1.{u} d hd a b hb hab ha
  refine ⟨G, hG, H, hH, N, hN, ?_⟩
  intro δstar hs hh
  obtain ⟨L, hL, bounds⟩ := hc δstar hs hh
  refine ⟨L, hL, ?_⟩
  intro δ hδ hcut n hn ψ hψ
  obtain ⟨he, hm, _⟩ := LocalCertification.Paper.history_budget_equivalence.{u}
    (spherePureVector ψ) a b δ
  rw [he, hm]
  exact bounds n hn ψ hψ δ hδ hcut

/-- At a step point the strict inequality selects the next integer degree. -/
example (d j : ℕ) (hd : 2 ≤ d) :
    sInf {k : ℕ | LocalCertification.Manuscript.gamma d k <
      LocalCertification.Manuscript.gamma d j} = j + 1 :=
  LocalCertification.Manuscript.physical_critical_boundary d hd j

/-- At the upper endpoint of the fidelity promise the exponent is zero. -/
example (d : ℕ) (hd : 2 ≤ d) (b : ℝ) (hb : b < 1) :
    sInf {k : ℕ | LocalCertification.Manuscript.gamma d k < (1-b)/(1-b)} = 0 :=
  LocalCertification.Manuscript.criticalDegree_at_unit_fidelity d
    (by exact_mod_cast (show 0 < d by omega)) b hb

end LocalCertification.Protocol.MeasurableExecution.ProductBudget

#eval IO.println "ToleranceHierarchyStatements_PASS"
