import LocalCertification.Protocol.MeasurableCalibratedBudget
import LocalCertification.Protocol.MeasurableConstantLowerBound
import LocalCertification.Quantum.MeasurableExponentialHardStates
import LocalCertification.Protocol.ExponentialLowerBound

/-! # Power lower bounds for arbitrary measurable product protocols

The actual calibrated hard pair supplies a uniform information bound on a
single compact target event. Optimizing over every allowed product protocol
preserves the exact binary testing factor, including infinite expected costs.
The degree-zero branch holds for every target. The exponential absorption lemma
is scalar; the protocol lower bound applies to all measurable product measurements.
-/

set_option autoImplicit false
open MeasureTheory Filter Metric CertificationGaussian LocalCertification.Information
  LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u

/-- A compact exponentially typical target event, fixed before confidence,
gives the exact lower scale for the full measurable product model. -/
theorem product_budget_power_lower_eventually (d r : ℕ) (hd : 2 ≤ d) [NeZero d]
    (a b : ℝ) (ha : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hwindow : r = 0 ∨ (a-b)/(1-b) ≤ gamma ((d:ℝ)+1) (r-1)) :
    ∃ c cprob : ℝ, 0 < c ∧ 0 < cprob ∧ ∀ᶠ n : ℕ in atTop,
      ∃ good : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1), IsCompact good ∧
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) goodᶜ ≤
          ENNReal.ofReal (Real.exp (-cprob*n)) ∧
        ∀ ψ ∈ good, ∀ δ : ℝ, 0 < δ → δ < 1/2 →
          ENNReal.ofReal (c*(n:ℝ)^r*testingThreshold δ) ≤
            expectedBudget.{u} (spherePureVector ψ) a b δ ∧
          expectedBudget.{u} (spherePureVector ψ) a b δ ≤
            ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) := by
  by_cases hr : r = 0
  · subst r
    have hΓ : 0 < 4/b+2 := by positivity
    refine ⟨1/(4/b+2),1,by positivity,by norm_num,?_⟩
    filter_upwards [constant_budget_bounds_eventually.{u} d hd b hb0 hb1] with n hn
    refine ⟨Set.univ,isCompact_univ,?_,?_⟩
    · simp only [Set.compl_univ, measure_empty]
      exact bot_le
    · intro ψ _ δ hδ hhalf
      have h := hn (spherePureVector ψ) a ha δ hδ hhalf
      rw [← ENNReal.ofReal_div_of_pos hΓ] at h
      refine ⟨?_,h.2⟩
      have he : (1/(4/b+2))*(n:ℝ)^0*testingThreshold δ = testingThreshold δ/(4/b+2) := by ring
      rw [he]
      exact h.1
  · have hj : r-1+1 = r := by omega
    have hgap : (a-b)/(1-b) ≤ gamma ((d:ℝ)+1) (r-1) := hwindow.resolve_left hr
    obtain ⟨C,K,_hC,hK,hgood⟩ := measurableExponential_hard_states.{u} hd (r-1) b hb0 hb1
    have hlog : 0 < Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
    refine ⟨1/K,min (Real.log (d:ℝ)/4) (Real.log (d:ℝ)/16)/2,by positivity,by positivity,?_⟩
    filter_upwards [hgood,eventually_ge_atTop 1,
      Protocol.exponential_failure_absorb (((r-1+1:ℕ):ℝ)) (Real.log (d:ℝ)/4)
        (Real.log (d:ℝ)/16) (by positivity) (by positivity) (by positivity)] with n hn hn1 hfail
    obtain ⟨hN,hcompact,hprob,hpair⟩ := hn
    refine ⟨measurableDualSphereGoodEvent hd (r-1) hN (exponentialOverlapCutoff d n),hcompact,?_,?_⟩
    · rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hprob
      exact hprob.trans (ENNReal.ofReal_le_ofReal hfail)
    · intro ψ hψ δ hδ hhalf
      obtain ⟨hlb,_hlo,_hhi,hinfo⟩ := hpair ψ hψ
      have h := calibrated_budget_power_bounds hd (r-1) hn1 (spherePureVector ψ) hN a b δ
        hb0 hb1 hlb hgap hδ hhalf K hK (fun Ω _ M => (hinfo Ω M).2)
      refine ⟨?_,h.2⟩
      have he : (1/K)*(n:ℝ)^r*testingThreshold δ = (testingThreshold δ/K)*(n:ℝ)^(r-1+1) := by
        rw [hj]
        ring
      rw [he]
      exact h.1

end LocalCertification.Protocol.MeasurableExecution.ProductBudget
