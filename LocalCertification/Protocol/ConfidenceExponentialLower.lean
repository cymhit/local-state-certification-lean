import LocalCertification.Protocol.ExponentialLowerBound
import LocalCertification.Protocol.ConfidenceConstantLower

set_option autoImplicit false
open MeasureTheory InformationTheory Filter Metric LocalCertification.Information LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The exact physical calibrated pair yields the critical lower budget on an exponentially likely
actual Haar target event, for every error level simultaneously. Degree r here yields order r+1. -/
theorem exponentialHaar_budget_lower_confidence {d : ℕ} [NeZero d] (hd : 2≤d) (r : ℕ)
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2) :
    ∃ clower cprob C : ℝ,0<clower ∧ 0<cprob ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      ∃ hN : (quditDualCertificate hd r).maxNode≤n,
      MeasurableSet (dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n)) ∧
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
        (dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n))ᶜ≤
          ENNReal.ofReal (Real.exp (-cprob*n)) ∧
      ∀ W∈dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n),
        ∀ a δ : ℝ,(a-b)/(1-b)≤gamma ((d:ℝ)+1) r → 0<δ → δ≤δstar →
          ENNReal.ofReal (clower*(n:ℝ)^(r+1)*Real.log (1/δ))≤expectedBudget (haarPureVector ψ₀ W) a b δ ∧
          ENNReal.ofReal (clower*(n:ℝ)^(r+1)*Real.log (1/δ))≤
            ENat.toENNReal (maximumBudget (haarPureVector ψ₀ W) a b δ) := by
  have hfac := confidenceFactor_pos δstar hs0 hshalf
  obtain ⟨c,C,K,hc,hC,hK,hgood⟩ := exponentialHaar_hard_states hd r b hb0 hb1
  have hlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  refine ⟨confidenceFactor δstar/K,min (Real.log (d:ℝ)/4) c/2, C,by positivity,by positivity,hC,?_⟩
  filter_upwards [hgood,eventually_ge_atTop 1,
    exponential_failure_absorb ((r+1:ℕ):ℝ) (Real.log (d:ℝ)/4) c (by positivity) (by positivity) hc]
    with n hn hn1 hfail
  intro ψ₀
  obtain ⟨hN,hm,hprob,hpair⟩ := hn ψ₀
  refine ⟨hN,hm,?_,?_⟩
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hprob
    exact hprob.trans (ENNReal.ofReal_le_ofReal hfail)
  · intro W hW a δ hgap hδ hcut
    obtain ⟨hlb,_hlo,_hhi,hL⟩ := hpair W hW
    have hp := calibratedNumerator_promised hd r (haarPureVector ψ₀ W) hN a b hb0 hb1 hlb hgap
    have he : ENNReal.ofReal ((confidenceFactor δstar/K)*(n:ℝ)^(r+1)*Real.log (1/δ))≤
        expectedBudget (haarPureVector ψ₀ W) a b δ := by
      apply expectedBudget_lower
      intro Q hv
      have hraw := expected_cost_power_lower K (testingThreshold δ) hK n r hn1 _
        (calibrated_terminal_information hd r _ hN a b δ hb0 hb1 hlb hgap hδ (by linarith) Q.toRaw hv _ hL)
      have ht := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (testingThreshold_confidence_lower δstar hs0 hshalf δ hδ hcut) hK.le)
        (show (0:ℝ)≤(n:ℝ)^(r+1) by positivity)
      have halgebra : (confidenceFactor δstar/K)*(n:ℝ)^(r+1)*Real.log (1/δ)≤(testingThreshold δ/K)*(n:ℝ)^(r+1) := by
        convert ht using 1
        field_simp
      exact ((ENNReal.ofReal_le_ofReal halgebra).trans hraw).trans
        (expectedCopies_le_protocolCost Q.toRaw (haarPureVector ψ₀ W) a b _ hp)
    exact ⟨he,he.trans (expectedBudget_le_maximumBudget (haarPureVector ψ₀ W) a b δ)⟩

end LocalCertification.Protocol
