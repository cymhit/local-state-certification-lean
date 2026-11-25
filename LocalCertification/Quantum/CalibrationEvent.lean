import LocalCertification.Quantum.CommonHaarEvent

set_option autoImplicit false
open scoped BigOperators ENNReal Topology
open LocalCertification.Extremal MeasureTheory Metric Set Filter
noncomputable section
namespace LocalCertification.Quantum

/-- The actual overlap cutoff used for the calibrated hard states. -/
def dualOverlapCutoff (d n : ℕ) : ℝ := (n : ℝ)^3/(d : ℝ)^n

theorem dualOverlapCutoff_pos {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    0 < dualOverlapCutoff d n := by
  unfold dualOverlapCutoff
  positivity

theorem uniform_fidelity_le_dualOverlapCutoff {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    ((d : ℝ)^n)⁻¹ ≤ dualOverlapCutoff d n := by
  have hD : 0 < (d : ℝ)^n := pow_pos (by exact_mod_cast (by omega : 0 < d)) _
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : (1 : ℝ) ≤ (n : ℝ)^3 := one_le_pow₀ hn'
  simpa only [dualOverlapCutoff, one_div] using (div_le_div_iff_of_pos_right hD).mpr hp

theorem dualOverlapCutoff_tendsto {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (dualOverlapCutoff d) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (n : ℝ)^3/(d : ℝ)^n) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
    monomial_decay_tendsto (d : ℝ) (by exact_mod_cast (by omega : 1 < d)) 3

/-- The polynomial cutoff gives the paper's explicit shell failure probability. -/
theorem dualOverlapCutoff_failure_le {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) (r : ℕ) :
    ((r+1 : ℕ) : ℝ)/(dualOverlapCutoff d n*((d : ℝ)^n+1)) ≤
      ((r+1 : ℕ) : ℝ)/(n : ℝ)^3 := by
  have hD : 0 < (d : ℝ)^n := pow_pos (by exact_mod_cast (by omega : 0 < d)) _
  have hn' : 0 < (n : ℝ)^3 := by positivity
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hn'
  unfold dualOverlapCutoff
  have h := div_pos hn' hD
  field_simp
  nlinarith

/-- For every fixed positive baseline, one measurable all-bases event has the required failure
bound and already makes the actual low overlap strictly smaller than that baseline. -/
theorem calibratedHaar_common_event {d : ℕ} [NeZero d] (hd : 2 ≤ d) (r : ℕ)
    (b : ℝ) (hb : 0 < b) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      MeasurableSet (dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n)) ∧
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
          (dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n))ᶜ ≤
        ENNReal.ofReal (((r+1 : ℕ) : ℝ)/(n : ℝ)^3) + ENNReal.ofReal (Real.exp (-a*(n : ℝ)^3)) ∧
      ∀ W ∈ dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n),
        uncalibratedLowFidelity hd r (haarPureVector ψ W) hN ≤ dualOverlapCutoff d n ∧
        uncalibratedLowFidelity hd r (haarPureVector ψ W) hN < b := by
  obtain ⟨a,C,ha,hC,N,hN⟩ := dualHaar_common_event hd r
  obtain ⟨N',hN'⟩ := eventually_atTop.mp ((dualOverlapCutoff_tendsto hd).eventually (gt_mem_nhds hb))
  refine ⟨a,C,ha,hC,max (max N N') 1,?_⟩
  intro n hn ψ
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN' : N' ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  obtain ⟨hmax, hprob⟩ := hN n hnN ψ _ (dualOverlapCutoff_pos hd hn1)
  refine ⟨hmax,dualHaarGoodEvent_measurableSet hd r ψ hmax C _,?_,?_⟩
  · exact hprob.trans (add_le_add (ENNReal.ofReal_le_ofReal (dualOverlapCutoff_failure_le hd hn1 r)) le_rfl)
  · intro W hW
    have hlow := dualHaarGoodEvent_low_fidelity hd r ψ hmax C _
      (uniform_fidelity_le_dualOverlapCutoff hd hn1) W hW
    exact ⟨hlow, hlow.trans_lt (hN' n hnN')⟩

end LocalCertification.Quantum
