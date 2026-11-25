import LocalCertification.Protocol.FixedBlockBudgets
import LocalCertification.Protocol.SphereHierarchy
import LocalCertification.Extremal.DegreeZero

set_option autoImplicit false
open MeasureTheory Metric Filter Set LocalCertification.Quantum CertificationGaussian LocalCertification.Asymptotic LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- A positive fixed block size gives a genuine local qudit dimension at least two. -/
theorem fixedBlock_dimension_ge_two (k : ℕ) (hk : 1≤k) : 2≤2^k := by
  simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<2) hk

/-- Corollary6.2, its actual physical fixed-block budgets. For every prescribed partition at each
system size, one compact physical Haar-typical target set works for all error levels simultaneously.
The partition never occurs among the adaptive action labels. -/
theorem fixedBlock_hierarchy (k : ℕ) (hk : 1≤k)
    (P : (m : ℕ) → FixedBlockPartition k m) (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree (((2^k : ℕ) : ℝ)+1) ((a-b)/(1-b))
    ∃ c C : ℝ,0<c ∧ 0<C ∧
    ∃ good : (m : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 (k*m))) 1),
      (∀ m,IsCompact (good m)) ∧
      Tendsto (fun m => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 (k*m))) (good m)) atTop (nhds 1) ∧
      ∀ᶠ m : ℕ in atTop,∀ ψ∈good m,∀ δ : ℝ,0<δ → δ≤1/3 →
        ENNReal.ofReal (c*(m:ℝ)^r*Real.log (1/δ))≤fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ ∧
        fixedBlockExpectedBudget (P m) (spherePureVector ψ) a b δ≤
          ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (fixedBlockMaximumBudget (P m) (spherePureVector ψ) a b δ)≤
          ENNReal.ofReal (C*(m:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  obtain ⟨c,C,hc,hC,good,hcompact,hprob,hN⟩ :=
    qudit_theorem_one_one (2^k) (fixedBlock_dimension_ge_two k hk) a b hb hab ha
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

/-- The critical exponent is zero exactly above the strict block threshold. -/
theorem fixedBlock_degree_zero_iff (k : ℕ) (hk : 1≤k) (g : ℝ) (hg : 0<g) :
    criticalDegree (((2^k : ℕ) : ℝ)+1) g=0 ↔ 1/(((2^k : ℕ) : ℝ)+1)<g := by
  have hd : (2:ℝ)≤((2^k : ℕ):ℝ) := by exact_mod_cast fixedBlock_dimension_ge_two k hk
  have hq : 1<((2^k : ℕ):ℝ)+1 := by linarith
  rw [← Nat.le_zero,criticalDegree_le_iff _ hq g hg 0,gamma_zero _ hq,one_div]

/-- Equality belongs to degree one, not to the constant-budget region. -/
theorem fixedBlock_degree_at_threshold (k : ℕ) (hk : 1≤k) :
    criticalDegree (((2^k : ℕ) : ℝ)+1) (1/(((2^k : ℕ) : ℝ)+1))=1 := by
  have hd : (2:ℝ)≤((2^k : ℕ):ℝ) := by exact_mod_cast fixedBlock_dimension_ge_two k hk
  have hq : 1<((2^k : ℕ):ℝ)+1 := by linarith
  have h := criticalDegree_at_critical_value _ hq 0
  simpa only [gamma_zero _ hq,one_div,Nat.zero_add] using h

/-- At or below the boundary the actual critical degree is positive. -/
theorem fixedBlock_degree_positive_iff (k : ℕ) (hk : 1≤k) (g : ℝ) (hg : 0<g) :
    1≤criticalDegree (((2^k : ℕ) : ℝ)+1) g ↔ g≤1/(((2^k : ℕ) : ℝ)+1) := by
  have h := fixedBlock_degree_zero_iff k hk g hg
  constructor
  · intro hr
    by_contra hn
    have hz := h.mpr (lt_of_not_ge hn)
    omega
  · intro hle
    by_contra hn
    have hz : criticalDegree (((2^k : ℕ) : ℝ)+1) g=0 := by omega
    exact (not_lt_of_ge hle) (h.mp hz)

end LocalCertification.Protocol
