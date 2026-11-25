import LocalCertification.Protocol.MeasurableBudgetHierarchy
import LocalCertification.Protocol.NearCriticalProductAssembly
/-! # The general product hierarchy on actual Haar targets

The compact canonical target family is pulled back through the actual unitary
Haar orbit map. The same constants and dimension cutoff apply to every initial
unit vector. The budgets use the original Born measurement laws and retain
extended expectations and deterministic caps on every legal path.
-/

set_option autoImplicit false
open MeasureTheory Filter Metric CertificationGaussian LocalCertification.Information
  LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u
/-- Theorem 1 and exponential typicality for genuine unitary Haar targets,
with the exact binary testing factor on the whole confidence interval. -/
theorem product_budget_haar_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
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
          ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ))  := by
  dsimp only
  obtain ⟨c,C,cprob,hc,hC,hcprob,good,hcompact,hone,N,hNpos,hN⟩ :=
    product_budget_sphere_hierarchy.{u} d hd a b hb hab ha
  refine ⟨c,C,cprob,hc,hC,hcprob,good,hcompact,?_,N,hNpos,?_⟩
  · intro ψ₀
    have he (n : ℕ) : complexUnitaryHaar (QuditIndex d n)
        {U | complexUnitarySphereAction (QuditIndex d n) U (ψ₀ n) ∈ good n} =
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n) :=
      (compact_good_haar_measure (good n) (hcompact n) (ψ₀ n)).2
    simpa only [he] using hone
  · intro n hn ψ₀
    obtain ⟨hpre,hmap⟩ := compact_good_haar_measure (good n) (hcompact n) ψ₀
    have hbad : MeasurableSet {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∉ good n} :=
      hpre.isClosed.measurableSet.compl
    refine ⟨hbad,?_,?_⟩
    · have he : complexUnitaryHaar (QuditIndex d n)
          {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∉ good n} =
          canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ := by
        change complexUnitaryHaar (QuditIndex d n)
          {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ good n}ᶜ = _
        rw [prob_compl_eq_one_sub hpre.isClosed.measurableSet,hmap,
          prob_compl_eq_one_sub (hcompact n).isClosed.measurableSet]
      rw [he]
      exact (hN n hn).1
    · intro U hU δ hδ hhalf
      exact (hN n hn).2 (complexUnitarySphereAction (QuditIndex d n) U ψ₀) hU δ hδ hhalf
end LocalCertification.Protocol.MeasurableExecution.ProductBudget
