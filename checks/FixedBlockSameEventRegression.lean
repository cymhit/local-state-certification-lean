import LocalCertification.LegacyPaper
import Lean

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian
open LocalCertification.Asymptotic LocalCertification.Protocol
open scoped ENNReal Topology
noncomputable section

namespace LocalCertification.Checks.FixedBlockSameEvent

/-! Independent target type for the fixed-block basis model. Both confidence cutoffs
use the same compact target family and size threshold. -/

theorem full_physical_statement (k : ℕ) (hk : 1 ≤ k)
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
      ∀ δstar : ℝ, 0 < δstar → δstar < 1 / 2 →
        ∃ c : ℝ, 0 < c ∧
        ∀ m, N ≤ m → ∀ ψ ∈ good m, ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
          ENNReal.ofReal (c * (m : ℝ) ^ r * Real.log (1 / δ)) ≤
            fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
          fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ≤
            ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ≤
            ENNReal.ofReal (C * (m : ℝ) ^ r * Real.log (1 / δ)) := by
  exact LocalCertification.LegacyPaper.S22 k hk P a b hb hab ha

/-- Existing clients can still use the original fixed-cutoff interface. -/
theorem fixed_cutoff_interface (k : ℕ) (hk : 1 ≤ k)
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
      ∀ᶠ m : ℕ in atTop, ∀ ψ ∈ good m, ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
        ENNReal.ofReal (c * (m : ℝ) ^ r * Real.log (1 / δ)) ≤
          fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ≤
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (C * (m : ℝ) ^ r * Real.log (1 / δ)) := by
  exact fixedBlock_hierarchy_continuous_confidence k hk P a b hb hab ha δstar hs0 hshalf

/-- Both confidence ranges use the witnesses from the fixed-block basis hierarchy. -/
theorem two_cutoffs_share_witnesses (k : ℕ) (hk : 1 ≤ k)
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
    ∃ cThird cNearHalf : ℝ, 0 < cThird ∧ 0 < cNearHalf ∧
      (∀ m, N ≤ m → ∀ ψ ∈ good m, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
        ENNReal.ofReal (cThird * (m : ℝ) ^ r * Real.log (1 / δ)) ≤
          fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ≤
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (C * (m : ℝ) ^ r * Real.log (1 / δ))) ∧
      (∀ m, N ≤ m → ∀ ψ ∈ good m, ∀ δ : ℝ, 0 < δ → δ ≤ 49 / 100 →
        ENNReal.ofReal (cNearHalf * (m : ℝ) ^ r * Real.log (1 / δ)) ≤
          fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ≤
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (C * (m : ℝ) ^ r * Real.log (1 / δ))) := by
  dsimp only
  obtain ⟨C, cprob, hC, hcprob, good, hcompact, hprob, N, hbad, hcut⟩ :=
    LocalCertification.LegacyPaper.S22 k hk P a b hb hab ha
  obtain ⟨cThird, hcThird, hThird⟩ := hcut (1 / 3) (by norm_num) (by norm_num)
  obtain ⟨cNearHalf, hcNearHalf, hNearHalf⟩ := hcut (49 / 100) (by norm_num) (by norm_num)
  exact ⟨C, cprob, hC, hcprob, good, hcompact, hprob, N, hbad,
    cThird, cNearHalf, hcThird, hcNearHalf, hThird, hNearHalf⟩

-- These are applications of the existing strict-boundary declarations.
example (k : ℕ) (hk : 1 ≤ k) (g : ℝ) (hg : 0 < g) :
    criticalDegree (((2 ^ k : ℕ) : ℝ) + 1) g = 0 ↔
      1 / (((2 ^ k : ℕ) : ℝ) + 1) < g :=
  fixedBlock_degree_zero_iff k hk g hg

example (k : ℕ) (hk : 1 ≤ k) :
    criticalDegree (((2 ^ k : ℕ) : ℝ) + 1)
      (1 / (((2 ^ k : ℕ) : ℝ) + 1)) = 1 :=
  fixedBlock_degree_at_threshold k hk

example (k : ℕ) (hk : 1 ≤ k) (g : ℝ) (hg : 0 < g) :
    1 ≤ criticalDegree (((2 ^ k : ℕ) : ℝ) + 1) g ↔
      g ≤ 1 / (((2 ^ k : ℕ) : ℝ) + 1) :=
  fixedBlock_degree_positive_iff k hk g hg

end LocalCertification.Checks.FixedBlockSameEvent

-- Compare elaborated types, including every parameter, without comparing text.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  for (publicName, sourceName) in [
      (`LocalCertification.LegacyPaper.theorem_1,
        `LocalCertification.Protocol.qudit_same_event_continuous_confidence_hierarchy),
      (`LocalCertification.LegacyPaper.theorem_2,
        `LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion)] do
    let some publicDecl := env.find? publicName | throwError "Missing public theorem: {publicName}"
    let some sourceDecl := env.find? sourceName | throwError "Missing source theorem: {sourceName}"
    unless publicDecl.type == sourceDecl.type do
      throwError "Public theorem type differs from the target type: {publicName}"
  logInfo "FIXED_BLOCK_SAME_EVENT_REGRESSION_PASS"
