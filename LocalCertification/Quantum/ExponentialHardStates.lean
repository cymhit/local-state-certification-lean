import LocalCertification.Quantum.ExponentialCalibrationScale

set_option autoImplicit false
open LocalCertification.Extremal Matrix MeasureTheory InformationTheory Filter Metric Set
open scoped Topology ENNReal
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

/-- The same actual calibrated pair and all-basis event work for every positive overlap cutoff. -/
theorem calibratedHaarGoodEvent_klDiv_cutoff (hd : 2≤d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode≤n) (C t : ℝ) (ht : 0≤t)
    (hDsmall : ((d:ℝ)^n)⁻¹≤t) (W : CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n))
    (hW : W∈dualHaarGoodEvent hd r ψ hN C t)
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1)
    (hlb : uncalibratedLowFidelity hd r (haarPureVector ψ W) hN<b)
    (U : Fin n → CertificationGaussian.LocalUnitary d) :
    klDiv (productBornMeasure d n U (calibratedNumeratorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb))
      (productBornMeasure d n U (calibratedDenominatorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb))≤
      ENNReal.ofReal (2*calibratedUniformWeight hd r b*(1+C/n)*
        CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r))+
        (4/calibratedUniformWeight hd r b)*((d:ℝ)^n*t^2)) := by
  apply (calibrated_productBorn_klDiv hd r (haarPureVector ψ W) hN b hb0 hb1 hlb U).trans
  apply ENNReal.ofReal_le_ofReal
  have hβ := calibratedUniformWeight_pos hd r hb1
  have he := calibrated_error_bounds hd r (haarPureVector ψ W) hN b hb0 hb1 hlb
  have hl := dualHaarGoodEvent_low_fidelity hd r ψ hN C t hDsmall W hW
  have hs : (b-calibrationAlpha b (uncalibratedLowFidelity hd r (haarPureVector ψ W) hN))^2≤t^2 :=
    (sq_le_sq₀ he.1 ht).mpr (he.2.trans hl)
  have h1 := mul_le_mul_of_nonneg_left (hW.2 U) (show 0≤2*calibratedUniformWeight hd r b by positivity)
  have h2 := mul_le_mul_of_nonneg_left hs (show 0≤4*(d:ℝ)^n/calibratedUniformWeight hd r b by positivity)
  change 2*calibratedUniformWeight hd r b*(d:ℝ)^n*‖CertificationGaussian.processedProbability
    (tensorBasis d n (qitProductBasis d n U))
    (CertificationGaussian.signedHammingKernel d n (residualRadii (quditDualCertificate hd r))
      (residualWeight d (quditDualCertificate hd r)))
    (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ)‖^2+_≤_
  convert add_le_add h1 h2 using 1 <;> ring

omit [NeZero d] in
/-- The changed physical cutoff preserves the actual one-copy information order n^(-r-1). -/
theorem exponentialInformationScale_eventually (hd : 2≤d) (r : ℕ)
    (b : ℝ) (hb1 : b<1) (C : ℝ) (hC : 0≤C) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      2*calibratedUniformWeight hd r b*(1+C/n)*
        CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r))+
        (4/calibratedUniformWeight hd r b)*((d:ℝ)^n*(exponentialOverlapCutoff d n)^2)≤K/(n:ℝ)^(r+1) := by
  obtain ⟨a,A,_ha,hA,N,hv⟩ := dualResidualKernel_power_order hd (quditDualCertificate hd r)
  have hlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  have ht := nat_pow_exp_decay (Real.log (d:ℝ)/2) (by positivity) (r+1)
  have hβ := calibratedUniformWeight_pos hd r hb1
  refine ⟨2*calibratedUniformWeight hd r b*(1+C)*A+4/calibratedUniformWeight hd r b,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop N,eventually_ge_atTop 1,
    ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1))] with n hnN hn1 hnsmall
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn1
  have hnp : 0<(n:ℝ)^(r+1) := pow_pos (by linarith) _
  have hsmall : (d:ℝ)^n*(exponentialOverlapCutoff d n)^2≤1/(n:ℝ)^(r+1) := by
    rw [exponentialOverlapCutoff_square_dimension d n (by omega)]
    exact (le_div_iff₀ hnp).mpr (by simpa only [mul_comm] using hnsmall)
  have hpref : C/(n:ℝ)≤C := div_le_self hC hnR
  have hfirst : 2*calibratedUniformWeight hd r b*(1+C/n)*
      CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
        (residualWeight d (quditDualCertificate hd r))≤
      (2*calibratedUniformWeight hd r b*(1+C)*A)/(n:ℝ)^(r+1) := by
    calc
      _≤2*calibratedUniformWeight hd r b*(1+C/n)*(A/(n:ℝ)^(r+1)) :=
        mul_le_mul_of_nonneg_left (hv n hnN).2 (by positivity)
      _≤2*calibratedUniformWeight hd r b*(1+C)*(A/(n:ℝ)^(r+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1+C/(n:ℝ)≤1+C)
          (by positivity)) (by positivity)
      _=_ := by ring
  have hsecond := mul_le_mul_of_nonneg_left hsmall
    (show 0≤4/calibratedUniformWeight hd r b by positivity)
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

/-- Actual promised calibrated hard states with exponentially small shell failure. The event still
controls every continuous product basis; all constants precede the target and the unknown input. -/
theorem exponentialHaar_hard_states (hd : 2≤d) (r : ℕ)
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) :
    ∃ c C K : ℝ,0<c ∧ 0<C ∧ 0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      ∃ hN : (quditDualCertificate hd r).maxNode≤n,
      MeasurableSet (dualHaarGoodEvent hd r ψ hN C (exponentialOverlapCutoff d n)) ∧
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
        (dualHaarGoodEvent hd r ψ hN C (exponentialOverlapCutoff d n))ᶜ≤
          ENNReal.ofReal (((r+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*n))+
          ENNReal.ofReal (Real.exp (-c*(n:ℝ)^3)) ∧
      ∀ W∈dualHaarGoodEvent hd r ψ hN C (exponentialOverlapCutoff d n),
        ∃ hlb : uncalibratedLowFidelity hd r (haarPureVector ψ W) hN<b,
        pureTargetFidelity (haarPureVector ψ W)
          (calibratedLowState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb)=b ∧
        b+(1-b)*gamma ((d:ℝ)+1) r≤pureTargetFidelity (haarPureVector ψ W)
          (calibratedHighState hd r (haarPureVector ψ W) hN b hb0 hb1) ∧
        ∀ U : Fin n → CertificationGaussian.LocalUnitary d,
          klDiv (productBornMeasure d n U (calibratedNumeratorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb))
            (productBornMeasure d n U (calibratedDenominatorState hd r (haarPureVector ψ W) hN b hb0 hb1 hlb))≤
            ENNReal.ofReal (K/(n:ℝ)^(r+1)) := by
  obtain ⟨c,C,hc,hC,N,hgood⟩ := dualHaar_common_event hd r
  obtain ⟨K,hK,hscale⟩ := exponentialInformationScale_eventually hd r b hb1 C hC.le
  refine ⟨c,C,K,hc,hC,hK,?_⟩
  filter_upwards [eventually_ge_atTop N,hscale,
    (exponentialOverlapCutoff_tendsto d hd).eventually (gt_mem_nhds hb0)] with n hn hs ht
  intro ψ
  obtain ⟨hN,hprob⟩ := hgood n hn ψ _ (exponentialOverlapCutoff_pos d n)
  refine ⟨hN,dualHaarGoodEvent_measurableSet hd r ψ hN C _,?_,?_⟩
  · exact hprob.trans (add_le_add (ENNReal.ofReal_le_ofReal (exponentialOverlapCutoff_failure_le d n r hd)) le_rfl)
  · intro W hW
    have hDsmall := uniform_fidelity_le_exponentialOverlapCutoff d n hd
    have hlb := (dualHaarGoodEvent_low_fidelity hd r ψ hN C _ hDsmall W hW).trans_lt ht
    refine ⟨hlb,calibratedLowState_fidelity hd r _ hN b hb0 hb1 hlb,
      calibratedHighState_fidelity hd r _ hN b hb0 hb1,?_⟩
    intro U
    exact (calibratedHaarGoodEvent_klDiv_cutoff hd r ψ hN C _ (exponentialOverlapCutoff_pos d n).le
      hDsmall W hW b hb0 hb1 hlb U).trans (ENNReal.ofReal_le_ofReal hs)

end LocalCertification.Quantum
