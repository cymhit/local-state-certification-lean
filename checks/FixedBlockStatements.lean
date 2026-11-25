import LocalCertification.Paper
import LocalCertification.Protocol.MeasurableFixedBlockHierarchy
import LocalCertification.Protocol.MeasurableFixedBlockBudgets
import LocalCertification.Protocol.FixedBlockConsequences
import LocalCertification.Information.ConfidenceRange

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian LocalCertification.Asymptotic
  LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.FixedBlock
universe u
example (k : ℕ) (hk : 1≤k)
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
  exact LocalCertification.Paper.fixed_block_testing_bounds.{u} k hk P a b hb hab ha

example (k : ℕ) (hk : 1≤k)
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
  exact LocalCertification.Paper.fixed_block_hierarchy.{u} k hk P a b hb hab ha

example (k : ℕ) (hk : 1≤k)
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
  exact LocalCertification.Paper.fixed_block_threshold.{u} k hk P a b hb hab ha

end LocalCertification.Protocol.MeasurableExecution.FixedBlock

#eval IO.println "FixedBlockStatements_PASS"
