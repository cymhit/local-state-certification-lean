import LocalCertification.Paper
import LocalCertification.Protocol.MeasurableHaarHierarchy
import LocalCertification.Protocol.MeasurableBudgetHierarchy
import LocalCertification.Protocol.NearCriticalProductAssembly

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
      (∀ ψ₀ : (n : ℕ) → sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
        Tendsto (fun n => complexUnitaryHaar (QuditIndex d n)
          {U | complexUnitarySphereAction (QuditIndex d n) U (ψ₀ n) ∈ good n}) atTop (nhds 1)) ∧
    ∃ N : ℕ, 1≤N ∧ ∀ n, N≤n →
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∉ good n} ∧
      complexUnitaryHaar (QuditIndex d n)
        {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∉ good n} ≤
          ENNReal.ofReal (Real.exp (-cprob*n)) ∧
      ∀ U, complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ good n →
        ∀ δ : ℝ, 0<δ → δ<1/2 →
        ENNReal.ofReal (c*(n:ℝ)^r*testingThreshold δ) ≤ expectedBudget.{u} (haarPureVector ψ₀ U) a b δ ∧
        expectedBudget.{u} (haarPureVector ψ₀ U) a b δ ≤ ENat.toENNReal (maximumBudget.{u} (haarPureVector ψ₀ U) a b δ) ∧
        ENat.toENNReal (maximumBudget.{u} (haarPureVector ψ₀ U) a b δ) ≤
          ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) :=
  LocalCertification.Paper.tolerance_haar_bounds d hd a b hb hab ha
end LocalCertification.Protocol.MeasurableExecution.ProductBudget

#eval IO.println "HaarStatements_PASS"
