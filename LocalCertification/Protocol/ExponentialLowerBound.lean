import LocalCertification.Protocol.PowerLowerBound
import LocalCertification.Quantum.ExponentialHardStates

set_option autoImplicit false
open MeasureTheory InformationTheory Filter Metric LocalCertification.Information LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- A fixed shell coefficient and the faster product-basis failure absorb into one exponential. -/
theorem exponential_failure_absorb (A rate c : ℝ) (hA : 0≤A) (hrate : 0<rate) (hc : 0<c) :
    ∀ᶠ n : ℕ in atTop,A*Real.exp (-rate*n)+Real.exp (-c*(n:ℝ)^3)≤
      Real.exp (-(min rate c/2)*n) := by
  let β := min rate c
  have hβ : 0<β := lt_min hrate hc
  have ht : Tendsto (fun n : ℕ => (A+1)*Real.exp (-(β/2)*n)) atTop (nhds 0) := by
    simpa only [pow_zero,one_mul,mul_zero] using
      tendsto_const_nhds.mul (nat_pow_exp_decay (β/2) (by positivity) 0)
  filter_upwards [eventually_ge_atTop 1,ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn hs
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hpow : (n:ℝ)≤(n:ℝ)^3 := by
    calc
      (n:ℝ)=(n:ℝ)*1 := by ring
      _≤(n:ℝ)*(n:ℝ)^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hnR) hn0
      _=(n:ℝ)^3 := by ring
  have hβrate : β≤rate := min_le_left _ _
  have hβc : β≤c := min_le_right _ _
  have h1 : Real.exp (-rate*n)≤Real.exp (-β*n) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (-c*(n:ℝ)^3)≤Real.exp (-β*n) := Real.exp_le_exp.mpr (by nlinarith)
  have hid : Real.exp (-β*n)=Real.exp (-(β/2)*n)*Real.exp (-(β/2)*n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _≤A*Real.exp (-β*n)+Real.exp (-β*n) := add_le_add (mul_le_mul_of_nonneg_left h1 hA) h2
    _=(A+1)*Real.exp (-(β/2)*n)*Real.exp (-(β/2)*n) := by rw [hid];ring
    _≤1*Real.exp (-(β/2)*n) := mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _=_ := by rw [one_mul]

/-- The exact physical calibrated pair yields the critical lower budget on an exponentially likely
actual Haar target event, for every error level simultaneously. Degree r here yields order r+1. -/
theorem exponentialHaar_budget_lower {d : ℕ} [NeZero d] (hd : 2≤d) (r : ℕ)
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) :
    ∃ clower cprob C : ℝ,0<clower ∧ 0<cprob ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      ∃ hN : (quditDualCertificate hd r).maxNode≤n,
      MeasurableSet (dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n)) ∧
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
        (dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n))ᶜ≤
          ENNReal.ofReal (Real.exp (-cprob*n)) ∧
      ∀ W∈dualHaarGoodEvent hd r ψ₀ hN C (exponentialOverlapCutoff d n),
        ∀ a δ : ℝ,(a-b)/(1-b)≤gamma ((d:ℝ)+1) r → 0<δ → δ≤1/3 →
          ENNReal.ofReal (clower*(n:ℝ)^(r+1)*Real.log (1/δ))≤expectedBudget (haarPureVector ψ₀ W) a b δ ∧
          ENNReal.ofReal (clower*(n:ℝ)^(r+1)*Real.log (1/δ))≤
            ENat.toENNReal (maximumBudget (haarPureVector ψ₀ W) a b δ) := by
  obtain ⟨c,C,K,hc,hC,hK,hgood⟩ := exponentialHaar_hard_states hd r b hb0 hb1
  have hlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  refine ⟨1/(6*K),min (Real.log (d:ℝ)/4) c/2, C,by positivity,by positivity,hC,?_⟩
  filter_upwards [hgood,eventually_ge_atTop 1,
    exponential_failure_absorb ((r+1:ℕ):ℝ) (Real.log (d:ℝ)/4) c (by positivity) (by positivity) hc]
    with n hn hn1 hfail
  intro ψ₀
  obtain ⟨hN,hm,hprob,hpair⟩ := hn ψ₀
  refine ⟨hN,hm,?_,?_⟩
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hprob
    exact hprob.trans (ENNReal.ofReal_le_ofReal hfail)
  · intro W hW a δ hgap hδ hthird
    obtain ⟨hlb,_hlo,_hhi,hL⟩ := hpair W hW
    have hp := calibratedNumerator_promised hd r (haarPureVector ψ₀ W) hN a b hb0 hb1 hlb hgap
    have he : ENNReal.ofReal ((1/(6*K))*(n:ℝ)^(r+1)*Real.log (1/δ))≤
        expectedBudget (haarPureVector ψ₀ W) a b δ := by
      apply expectedBudget_lower
      intro Q hv
      have hraw := expected_cost_power_lower K (testingThreshold δ) hK n r hn1 _
        (calibrated_terminal_information hd r _ hN a b δ hb0 hb1 hlb hgap hδ (by linarith) Q.toRaw hv _ hL)
      have ht := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (testingThreshold_log_lower δ hδ hthird) hK.le)
        (show (0:ℝ)≤(n:ℝ)^(r+1) by positivity)
      have halgebra : (1/(6*K))*(n:ℝ)^(r+1)*Real.log (1/δ)≤(testingThreshold δ/K)*(n:ℝ)^(r+1) := by
        convert ht using 1
        field_simp
      exact ((ENNReal.ofReal_le_ofReal halgebra).trans hraw).trans
        (expectedCopies_le_protocolCost Q.toRaw (haarPureVector ψ₀ W) a b _ hp)
    exact ⟨he,he.trans (expectedBudget_le_maximumBudget (haarPureVector ψ₀ W) a b δ)⟩

end LocalCertification.Protocol
