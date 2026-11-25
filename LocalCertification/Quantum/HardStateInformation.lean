import LocalCertification.Quantum.CalibratedInformation

set_option autoImplicit false
open scoped BigOperators ENNReal Topology
open LocalCertification.Extremal Matrix MeasureTheory InformationTheory Metric Set Filter
noncomputable section
namespace LocalCertification.Quantum

/-- Explicit absorption of the exponentially small calibration term into the actual residual order. -/
theorem calibratedInformationScale_eventually {d : ℕ} (hd : 2 ≤ d) (r : ℕ)
    (b : ℝ) (hb1 : b < 1) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N,
      2*calibratedUniformWeight hd r b*(1+C/n)*
        CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r)) +
        (4/calibratedUniformWeight hd r b)*((n : ℝ)^6/(d : ℝ)^n) ≤ K/(n : ℝ)^(r+1) := by
  obtain ⟨a,A,ha,hA,N,hv⟩ := dualResidualKernel_power_order hd (quditDualCertificate hd r)
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(r+7)/(d : ℝ)^n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,inv_pow,mul_comm] using
      monomial_decay_tendsto (d : ℝ) (by exact_mod_cast (by omega : 1 < d)) (r+7)
  obtain ⟨N',hN'⟩ := eventually_atTop.mp (ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  have hβ := calibratedUniformWeight_pos hd r hb1
  refine ⟨2*calibratedUniformWeight hd r b*(1+C)*A+4/calibratedUniformWeight hd r b,by positivity,
    max N (max N' 1),?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN' : N' ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnp : 0 < (n : ℝ)^(r+1) := pow_pos (by linarith) _
  have hD : 0 < (d : ℝ)^n := pow_pos (by exact_mod_cast (by omega : 0 < d)) _
  have hsmall : (n : ℝ)^6/(d : ℝ)^n ≤ 1/(n : ℝ)^(r+1) := by
    apply (div_le_div_iff₀ hD hnp).mpr
    rw [← pow_add, show 6+(r+1)=r+7 by omega, one_mul]
    exact (div_le_one hD).mp (hN' n hnN')
  have hpref : C/(n : ℝ) ≤ C := div_le_self hC hnR
  have hfirst : 2*calibratedUniformWeight hd r b*(1+C/n)*
      CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
        (residualWeight d (quditDualCertificate hd r)) ≤
      (2*calibratedUniformWeight hd r b*(1+C)*A)/(n : ℝ)^(r+1) := by
    calc
      _ ≤ 2*calibratedUniformWeight hd r b*(1+C/n)*(A/(n : ℝ)^(r+1)) :=
        mul_le_mul_of_nonneg_left (hv n hnN).2 (by positivity)
      _ ≤ 2*calibratedUniformWeight hd r b*(1+C)*(A/(n : ℝ)^(r+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1+C/(n : ℝ) ≤ 1+C)
          (by positivity)) (by positivity)
      _ = _ := by ring
  have hsecond := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ 4/calibratedUniformWeight hd r b by positivity)
  calc
    _ ≤ (2*calibratedUniformWeight hd r b*(1+C)*A)/(n : ℝ)^(r+1)+
      (4/calibratedUniformWeight hd r b)*(1/(n : ℝ)^(r+1)) := add_le_add hfirst hsecond
    _ = _ := by ring

/-- Actual hard states on one measurable high-probability target event: exact low fidelity,
critical-boundary high fidelity, and uniform one-copy measure KL for every continuous product basis.
All constants and the system-size cutoff are chosen before the Haar target and the measurement. -/
theorem calibratedHaar_hard_states {d : ℕ} [NeZero d] (hd : 2 ≤ d) (r : ℕ)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ a C K : ℝ, 0 < a ∧ 0 < C ∧ 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      MeasurableSet (dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n)) ∧
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
          (dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n))ᶜ ≤
        ENNReal.ofReal (((r+1 : ℕ) : ℝ)/(n : ℝ)^3)+ENNReal.ofReal (Real.exp (-a*(n : ℝ)^3)) ∧
      ∀ W ∈ dualHaarGoodEvent hd r ψ hN C (dualOverlapCutoff d n),
        ∃ hlb : uncalibratedLowFidelity hd r (haarPureVector ψ W) hN < b,
        pureTargetFidelity (haarPureVector ψ W)
          (calibratedLowState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb) = b ∧
        b+(1-b)*gamma ((d : ℝ)+1) r ≤ pureTargetFidelity (haarPureVector ψ W)
          (calibratedHighState hd r (haarPureVector ψ W) hN b hb0 hb1) ∧
        ∀ U : Fin n → CertificationGaussian.LocalUnitary d,
          klDiv (productBornMeasure d n U
            (calibratedNumeratorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb))
            (productBornMeasure d n U
              (calibratedDenominatorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb)) ≤
            ENNReal.ofReal (K/(n : ℝ)^(r+1)) := by
  obtain ⟨a,C,ha,hC,N,hgood⟩ := calibratedHaar_common_event hd r b hb0
  obtain ⟨K,hK,N',hscale⟩ := calibratedInformationScale_eventually hd r b hb1 C hC.le
  refine ⟨a,C,K,ha,hC,hK,max (max N N') 1,?_⟩
  intro n hn ψ
  have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN' : N' ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hmax,hm,hprob,hlow⟩ := hgood n hnN ψ
  refine ⟨hmax,hm,hprob,?_⟩
  intro W hW
  have hlb := (hlow W hW).2
  refine ⟨hlb,calibratedLowState_fidelity hd r _ hmax b hb0 hb1 hlb,
    calibratedHighState_fidelity hd r _ hmax b hb0 hb1,?_⟩
  intro U
  exact (calibratedHaarGoodEvent_klDiv hd r ψ hmax C W hW hn1 b hb0 hb1 hlb U).trans
    (ENNReal.ofReal_le_ofReal (hscale n hnN'))

end LocalCertification.Quantum
