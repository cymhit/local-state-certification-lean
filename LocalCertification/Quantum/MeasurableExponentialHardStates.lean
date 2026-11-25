import LocalCertification.Quantum.MeasurableHardStateEvent
import LocalCertification.Quantum.ExponentialHardStates
import CertificationGaussian.ProductFrameCommonEvent

/-! Actual fixed calibrated hard states on one compact canonical target event.
The common event for all product frames controls arbitrary measurable product POVMs.
The failure estimate combines the finite-shell Markov bound with the scalar calibration bounds. -/
set_option autoImplicit false
open LocalCertification.Extremal MeasureTheory InformationTheory Matrix Metric Set Filter
open scoped ENNReal ComplexOrder Topology
noncomputable section
universe u
namespace LocalCertification.Quantum
variable {d : ℕ} [NeZero d]

/-- One cutoff in system size works for every initial Haar vector and every overlap cutoff. -/
theorem measurableDual_common_haar_eventually (hd : 2 ≤ d) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      ∀ (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
        (t : ℝ), 0 < t →
        CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
          (measurableDualHaarGoodEvent hd r ψ hN t)ᶜ ≤
          ENNReal.ofReal (((r+1:ℕ):ℝ)/(t*((d:ℝ)^n+1))) +
            ENNReal.ofReal (Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3)) := by
  filter_upwards [CertificationGaussian.productFrame_common_haar_eventually hd
    (residualRadii (quditDualCertificate hd r)) (residualWeight d (quditDualCertificate hd r))
    (residualWeight_mass d (by omega) (quditDualCertificate hd r)),
    eventually_ge_atTop (quditDualCertificate hd r).maxNode] with n hframe hN
  refine ⟨hN, ?_⟩
  intro ψ t ht
  have hs := dualHaar_shell_failure hd r ψ hN ht
  have hf := hframe ψ
  apply le_trans (measure_mono (show (measurableDualHaarGoodEvent hd r ψ hN t)ᶜ ⊆
      {U | ∃ i : Fin (r+1), t < pureTargetFidelity (haarPureVector ψ U)
        (pureTargetShell hd (haarPureVector ψ U) ((quditDualCertificate hd r).node i)
          (((quditDualCertificate hd r).node_le_maxNode i).trans hN))} ∪
      {U | ¬ ∀ T ∈ CertificationGaussian.signedProductFrameFamily (S := Fin n) (I := Fin d)
        (residualRadii (quditDualCertificate hd r)) (residualWeight d (quditDualCertificate hd r)),
        CertificationGaussian.gaussianFrameSphereScore T
          (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) U ψ) ≤
          (1+6/(n:ℝ))*CertificationGaussian.kernelVarianceScale d n
            (residualRadii (quditDualCertificate hd r)) (residualWeight d (quditDualCertificate hd r))} from ?_))
  · exact (measure_union_le _ _).trans (add_le_add hs hf)
  · intro U hU
    change ¬ (_ ∧ _) at hU
    rcases not_and_or.mp hU with hs | hf
    · left
      change ¬ ∀ i : Fin (r+1), pureTargetFidelity (haarPureVector ψ U)
        (pureTargetShell hd (haarPureVector ψ U) ((quditDualCertificate hd r).node i)
          (((quditDualCertificate hd r).node_le_maxNode i).trans hN)) ≤ t at hs
      simpa only [Set.mem_ofPred_eq, not_forall, not_le] using hs
    · exact Or.inr hf

/-- The same compact canonical target set has the actual sphere failure bound. -/
theorem measurableDual_common_sphere_eventually (hd : 2 ≤ d) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      ∀ t : ℝ, 0 < t →
        CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))
          (measurableDualSphereGoodEvent hd r hN t)ᶜ ≤
          ENNReal.ofReal (((r+1:ℕ):ℝ)/(t*((d:ℝ)^n+1))) +
            ENNReal.ofReal (Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3)) := by
  filter_upwards [measurableDual_common_haar_eventually hd r] with n hn
  obtain ⟨hN, hprob⟩ := hn
  refine ⟨hN, ?_⟩
  intro t ht
  obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty
    (E := EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))).mpr
      (show (0:ℝ) ≤ 1 by norm_num)
  have h := hprob ⟨z,hz⟩ t ht
  rw [measurableDualHaarGoodEvent_failure_eq] at h
  exact h

/-- Constants and one compact target family precede every local outcome space and POVM.
The promises and the information bounds use the same actual calibrated states. -/
theorem measurableExponential_hard_states (hd : 2 ≤ d) (r : ℕ)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      IsCompact (measurableDualSphereGoodEvent hd r hN (exponentialOverlapCutoff d n)) ∧
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))
        (measurableDualSphereGoodEvent hd r hN (exponentialOverlapCutoff d n))ᶜ ≤
        ENNReal.ofReal (((r+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*n)) +
          ENNReal.ofReal (Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3)) ∧
      ∀ ψ ∈ measurableDualSphereGoodEvent hd r hN (exponentialOverlapCutoff d n),
        ∃ hlb : uncalibratedLowFidelity hd r (spherePureVector ψ) hN < b,
        pureTargetFidelity (spherePureVector ψ)
          (calibratedLowState hd r (spherePureVector ψ) hN b hb0 hb1 hlb) = b ∧
        b+(1-b)*gamma ((d:ℝ)+1) r ≤ pureTargetFidelity (spherePureVector ψ)
          (calibratedHighState hd r (spherePureVector ψ) hN b hb0 hb1) ∧
        ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
          (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
          (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd r (spherePureVector ψ) hN b hb0 hb1) s -
            (MeasurablePOVM.product M).bornDensity (calibratedLowState hd r (spherePureVector ψ) hN b hb0 hb1 hlb) s)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ C/(n:ℝ)^(r+1) ∧
          klDiv ((MeasurablePOVM.product M).born (calibratedNumeratorState hd r (spherePureVector ψ) hN b hb0 hb1 hlb))
            ((MeasurablePOVM.product M).born (calibratedDenominatorState hd r (spherePureVector ψ) hN b hb0 hb1 hlb)) ≤
            ENNReal.ofReal (K/(n:ℝ)^(r+1)) := by
  obtain ⟨K,hK,hscale⟩ := exponentialInformationScale_eventually hd r b hb1 6 (by norm_num)
  have hβ := calibratedUniformWeight_pos hd r hb1
  refine ⟨calibratedUniformWeight hd r b*K, K, mul_pos hβ hK, hK, ?_⟩
  filter_upwards [measurableDual_common_sphere_eventually hd r, hscale,
    (exponentialOverlapCutoff_tendsto d hd).eventually (gt_mem_nhds hb0)] with n hcommon hscale ht
  obtain ⟨hN,hprob⟩ := hcommon
  refine ⟨hN, measurableDualSphereGoodEvent_isCompact hd r hN _, ?_, ?_⟩
  · exact (hprob _ (exponentialOverlapCutoff_pos d n)).trans
      (add_le_add (ENNReal.ofReal_le_ofReal (exponentialOverlapCutoff_failure_le d n r hd)) le_rfl)
  · intro ψ hψ
    have hD := uniform_fidelity_le_exponentialOverlapCutoff d n hd
    have hlb := (measurableDualSphereGoodEvent_low_fidelity hd r hN _ hD ψ hψ).trans_lt ht
    refine ⟨hlb, calibratedLowState_fidelity hd r _ hN b hb0 hb1 hlb,
      calibratedHighState_fidelity hd r _ hN b hb0 hb1, ?_⟩
    intro Ω _ M
    constructor
    · refine (measurableDualSphereGoodEvent_referenceL2_cutoff hd r hN _ hD ψ hψ b hb0 hb1 hlb M).trans ?_
      have he : 2*(calibratedUniformWeight hd r b)^2*(1+6/(n:ℝ))*
          CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
            (residualWeight d (quditDualCertificate hd r)) + 4*(d:ℝ)^n*(exponentialOverlapCutoff d n)^2 =
          calibratedUniformWeight hd r b * (2*calibratedUniformWeight hd r b*(1+6/(n:ℝ))*
          CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
            (residualWeight d (quditDualCertificate hd r)) +
          (4/calibratedUniformWeight hd r b)*((d:ℝ)^n*(exponentialOverlapCutoff d n)^2)) := by
        field_simp [hβ.ne']
      rw [he]
      exact (mul_le_mul_of_nonneg_left hscale hβ.le).trans_eq (by ring)
    · refine (measurableDualSphereGoodEvent_klDiv_cutoff hd r hN _ hD ψ hψ b hb0 hb1 hlb M).trans
        (ENNReal.ofReal_le_ofReal ?_)
      convert hscale using 1
      ring

end LocalCertification.Quantum
