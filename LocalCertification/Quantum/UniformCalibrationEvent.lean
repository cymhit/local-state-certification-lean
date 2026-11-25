import LocalCertification.Quantum.MeasurableExponentialHardStates

/-! The shell and product-frame event used for calibration in SM V.C is
independent of the fidelity threshold. Its quadratic bound is uniform
when the threshold ranges over a closed subinterval of `(0,1)`. -/

set_option autoImplicit false
open LocalCertification.Extremal MeasureTheory Metric Set Filter
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Quantum
universe u

theorem calibratedUniformWeight_antitone {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    Antitone (calibratedUniformWeight hd r) := by
  intro b₁ b₂ hb
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left hb 1)
    (uniformComponentWeight_pos (qudit_parameter_gt_one hd) _).le

/-- A single size cutoff places the overlap below the left endpoint and
keeps the calibration denominator at least one half throughout the interval. -/
theorem eventually_calibration_overlap_window {d : ℕ} (hd : 2 ≤ d)
    (bmin : ℝ) (hmin : 0 < bmin) : ∀ᶠ n : ℕ in atTop,
    exponentialOverlapCutoff d n < bmin ∧ exponentialOverlapCutoff d n ≤ 1/2 := by
  have ht := exponentialOverlapCutoff_tendsto d hd
  have h := ht.eventually (gt_mem_nhds (lt_min hmin (by norm_num : (0 : ℝ) < 1/2)))
  exact h.mono fun n hn => ⟨(lt_min_iff.mp hn).1, (lt_min_iff.mp hn).2.le⟩

/-- The event and cutoff precede the running threshold and every local
product POVM. The calibration error and retained background are controlled
by opposite endpoints of the threshold interval. -/
theorem measurableExponential_hard_states_uniform {d : ℕ} [NeZero d] (hd : 2 ≤ d) (r : ℕ)
    (bmin bmax : ℝ) (hmin : 0 < bmin) (hI : bmin ≤ bmax) (hmax : bmax < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      IsCompact (measurableDualSphereGoodEvent hd r hN (exponentialOverlapCutoff d n)) ∧
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))
        (measurableDualSphereGoodEvent hd r hN (exponentialOverlapCutoff d n))ᶜ ≤
        ENNReal.ofReal (((r+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*n)) +
          ENNReal.ofReal (Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3)) ∧
      ∀ ψ ∈ measurableDualSphereGoodEvent hd r hN (exponentialOverlapCutoff d n),
      ∀ b : ℝ, ∀ (hl : bmin ≤ b) (hu : b ≤ bmax),
        ∃ hlb : uncalibratedLowFidelity hd r (spherePureVector ψ) hN < b,
        ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
          (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
          (∫ s, ((MeasurablePOVM.product M).bornDensity
            (calibratedHighState hd r (spherePureVector ψ) hN b (hmin.trans_le hl) (hu.trans_lt hmax)) s -
            (MeasurablePOVM.product M).bornDensity
            (calibratedLowState hd r (spherePureVector ψ) hN b (hmin.trans_le hl) (hu.trans_lt hmax) hlb) s)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ C/(n:ℝ)^(r+1) := by
  obtain ⟨K, hK, hscale⟩ := exponentialInformationScale_eventually hd r bmin (hI.trans_lt hmax) 6 (by norm_num)
  have hβ := calibratedUniformWeight_pos hd r (hI.trans_lt hmax)
  refine ⟨calibratedUniformWeight hd r bmin * K, mul_pos hβ hK, ?_⟩
  filter_upwards [measurableDual_common_sphere_eventually hd r, hscale,
    eventually_calibration_overlap_window hd bmin hmin] with n hcommon hscale ht
  obtain ⟨hN, hprob⟩ := hcommon
  refine ⟨hN, measurableDualSphereGoodEvent_isCompact hd r hN _, ?_, ?_⟩
  · exact (hprob _ (exponentialOverlapCutoff_pos d n)).trans
      (add_le_add (ENNReal.ofReal_le_ofReal (exponentialOverlapCutoff_failure_le d n r hd)) le_rfl)
  · intro ψ hψ b hl hu
    have hD := uniform_fidelity_le_exponentialOverlapCutoff d n hd
    have hlb := (measurableDualSphereGoodEvent_low_fidelity hd r hN _ hD ψ hψ).trans_lt (ht.1.trans_le hl)
    refine ⟨hlb, ?_⟩
    intro Ω _ M
    refine (measurableDualSphereGoodEvent_referenceL2_cutoff hd r hN _ hD ψ hψ b
      (hmin.trans_le hl) (hu.trans_lt hmax) hlb M).trans ?_
    have hβb := calibratedUniformWeight_pos hd r (hu.trans_lt hmax)
    have hs := pow_le_pow_left₀ hβb.le (calibratedUniformWeight_antitone hd r hl) 2
    have hv := CertificationGaussian.kernelVarianceScale_nonneg d n
      (residualRadii (quditDualCertificate hd r)) (residualWeight d (quditDualCertificate hd r))
    calc
      _ ≤ 2*(calibratedUniformWeight hd r bmin)^2*(1+6/(n:ℝ))*_ + 4*(d:ℝ)^n*(exponentialOverlapCutoff d n)^2 := by
        gcongr
      _ = calibratedUniformWeight hd r bmin * (2*calibratedUniformWeight hd r bmin*(1+6/(n:ℝ))*
          CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
            (residualWeight d (quditDualCertificate hd r)) +
          (4/calibratedUniformWeight hd r bmin)*((d:ℝ)^n*(exponentialOverlapCutoff d n)^2)) := by
        field_simp [hβ.ne']
      _ ≤ _ := (mul_le_mul_of_nonneg_left hscale hβ.le).trans_eq (by ring)

end LocalCertification.Quantum

