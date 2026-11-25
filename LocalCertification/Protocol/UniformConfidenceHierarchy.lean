import LocalCertification.Information.ContinuousConfidenceRatio
import LocalCertification.Protocol.SameConfidenceEvent
import LocalCertification.Protocol.ProductDensityConfidenceEvent

set_option autoImplicit false
open MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Asymptotic LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The common target family and threshold are fixed before the confidence cutoff.
The bounds use the finite product-density terminal chain and the score and hard-state constructions. -/
theorem qudit_same_event_continuous_confidence_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ C cprob : ℝ,0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n,IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
    ∃ N : ℕ,
      (∀ n,N≤n → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤
        ENNReal.ofReal (Real.exp (-cprob*n))) ∧
      ∀ δstar : ℝ,0<δstar → δstar<1/2 → ∃ c : ℝ,0<c ∧
        ∀ n,N≤n → ∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤δstar →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
          expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤
            ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  obtain ⟨A,C,cprob,hA,hC,hcprob,good,hcompact,hN⟩ := qudit_exponential_testing_hierarchy_via_product_density d hd a b hb hab ha
  have hone := canonicalSphere_good_probability_tendsto_one d hd good hcompact cprob hcprob (hN.mono (fun _ h => h.1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hN
  refine ⟨C,cprob,hC,hcprob,good,hcompact,hone,N,fun n hn => (hN n hn).1,?_⟩
  intro δstar hs0 hshalf
  obtain ⟨k,hk,hcompare⟩ := testingThreshold_confidence_lower_via_continuous_ratio δstar hs0 hshalf
  refine ⟨A*k,mul_pos hA hk,?_⟩
  intro n hn ψ hψ δ hδ hcut
  obtain ⟨hlo,hmid,hup⟩ := (hN n hn).2 ψ hψ δ hδ (hcut.trans_lt hshalf)
  refine ⟨?_,hmid,hup⟩
  apply (ENNReal.ofReal_le_ofReal ?_).trans hlo
  have h := mul_le_mul_of_nonneg_left
    (hcompare δ hδ hcut)
    (show (0:ℝ)≤A*(n:ℝ)^r by positivity)
  convert h using 1
  ring

/-- The fixed-cutoff projection of the stronger common-family theorem, used by physical blocks. -/
theorem qudit_continuous_confidence_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C : ℝ,0<c ∧ 0<C ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n,IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
      ∀ᶠ n : ℕ in atTop,∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤δstar →
        ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ))≤expectedBudget (spherePureVector ψ) a b δ ∧
        expectedBudget (spherePureVector ψ) a b δ≤ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤
          ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  obtain ⟨C,cprob,hC,_hcprob,good,hcompact,hprob,N,_hbad,hcut⟩ :=
    qudit_same_event_continuous_confidence_hierarchy d hd a b hb hab ha
  obtain ⟨c,hc,hbound⟩ := hcut δstar hs0 hshalf
  exact ⟨c,C,hc,hC,good,hcompact,hprob,eventually_atTop.mpr ⟨N,hbound⟩⟩

end LocalCertification.Protocol
