import LocalCertification.LegacyPaper

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian
open LocalCertification.Asymptotic LocalCertification.Protocol
open scoped ENNReal Topology
noncomputable section

namespace LocalCertification.Checks.FixedBlockSameEventConsequences

/-!
The fixed-block proposition also identifies the strict zero-degree window and
states divergence at and below its boundary. This independent target requires
the logarithmic criterion and divergence on the very same physical sets as the
exponential hierarchy, with those sets chosen before any confidence cutoff.
-/

theorem full_same_family_consequences (k : ℕ) (hk : 1 ≤ k)
    (P : (m : ℕ) → FixedBlockPartition k m)
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (ha : a ≤ 1) :
    let r := criticalDegree (((2 ^ k : ℕ) : ℝ) + 1) ((a - b) / (1 - b))
    ∃ C cprob : ℝ, 0 < C ∧ 0 < cprob ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k * m))) 1),
      (∀ m, IsCompact (good m)) ∧
      Tendsto
        (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k * m))) (good m))
        atTop (nhds 1) ∧
    ∃ N : ℕ,
      (∀ m, N ≤ m →
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k * m))) (good m)ᶜ ≤
          ENNReal.ofReal (Real.exp (-cprob * m))) ∧
      (∀ δstar : ℝ, 0 < δstar → δstar < 1 / 2 →
        ∃ c : ℝ, 0 < c ∧
        ∀ m, N ≤ m → ∀ ψ ∈ good m, ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
          ENNReal.ofReal (c * (m : ℝ) ^ r * Real.log (1 / δ)) ≤
            fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
          fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ≤
            ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ≤
            ENNReal.ofReal (C * (m : ℝ) ^ r * Real.log (1 / δ))) ∧
      (∀ δstar : ℝ, 0 < δstar → δstar < 1 / 2 →
        (FixedBlockConfidenceLogBound P good a b δstar ↔
          1 / (((2 ^ k : ℕ) : ℝ) + 1) < (a - b) / (1 - b))) ∧
      ((a - b) / (1 - b) ≤ 1 / (((2 ^ k : ℕ) : ℝ) + 1) →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∀ B : ℝ≥0∞, B < ∞ →
          ∀ᶠ m : ℕ in atTop, ∀ ψ ∈ good m,
            B < fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
            B < ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)) := by
  exact LocalCertification.LegacyPaper.S22_criterion k hk P a b hb hab ha

/-- Fixed-confidence growth and divergence for product-basis protocols on a prescribed partition. -/
theorem legacy_fixed_cutoff_criterion (k : ℕ) (hk : 1 ≤ k)
    (P : (m : ℕ) → FixedBlockPartition k m)
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (ha : a ≤ 1)
    (δstar : ℝ) (hs0 : 0 < δstar) (hshalf : δstar < 1 / 2) :
    let r := criticalDegree (((2 ^ k : ℕ) : ℝ) + 1) ((a - b) / (1 - b))
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k * m))) 1),
      (∀ m, IsCompact (good m)) ∧
      Tendsto
        (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k * m))) (good m))
        atTop (nhds 1) ∧
      (∀ᶠ m : ℕ in atTop, ∀ ψ ∈ good m, ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
        ENNReal.ofReal (c * (m : ℝ) ^ r * Real.log (1 / δ)) ≤
          fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ≤
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (C * (m : ℝ) ^ r * Real.log (1 / δ))) ∧
      (FixedBlockConfidenceLogBound P good a b δstar ↔
        1 / (((2 ^ k : ℕ) : ℝ) + 1) < (a - b) / (1 - b)) := by
  exact fixedBlock_log_budget_criterion_continuous_confidence
    k hk P a b hb hab ha δstar hs0 hshalf

example (k : ℕ) (hk : 1 ≤ k) (g : ℝ) (hg : 0 < g) :
    criticalDegree (((2 ^ k : ℕ) : ℝ) + 1) g = 0 ↔
      1 / (((2 ^ k : ℕ) : ℝ) + 1) < g :=
  fixedBlock_degree_zero_iff k hk g hg

example (k : ℕ) (hk : 1 ≤ k) :
    criticalDegree (((2 ^ k : ℕ) : ℝ) + 1)
      (1 / (((2 ^ k : ℕ) : ℝ) + 1)) = 1 :=
  fixedBlock_degree_at_threshold k hk

end LocalCertification.Checks.FixedBlockSameEventConsequences

#eval IO.println "REGRESSION_CHECK\tFixedBlockSameEventConsequences\tPASS"
