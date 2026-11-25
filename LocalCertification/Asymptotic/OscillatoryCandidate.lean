import LocalCertification.Asymptotic.OscillatoryIntegral

open scoped Topology ContDiff
open MeasureTheory Set Real Complex

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section
namespace LocalCertification.Asymptotic

/-- The actual supremum norm of the amplitude on one full turn. -/
def amplitudeSupremum (a : ℝ) : ℝ :=
  sSup ((fun t : ℝ => ‖boundaryAmplitude a t‖) '' Icc 0 (2 * Real.pi))

/-- The actual total derivative variation of the amplitude. -/
def amplitudeVariation (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..(2 * Real.pi), ‖deriv (boundaryAmplitude a) t‖

/-- The precise constant supplied by the oscillatory estimate, with probability-circle normalization. -/
def upperOscillationConstant (a : ℝ) : ℝ :=
  (4 * amplitudeConstant a + 12 * amplitudeSupremum a + amplitudeVariation a) / (2 * Real.pi)

theorem amplitudeSupremum_bddAbove (a : ℝ) (ha : |a| < 1) :
    BddAbove ((fun t : ℝ => ‖boundaryAmplitude a t‖) '' Icc 0 (2 * Real.pi)) :=
  isCompact_Icc.bddAbove_image (boundaryAmplitude_contDiff a ha).continuous.norm.continuousOn

theorem amplitude_le_supremum (a : ℝ) (ha : |a| < 1) (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
    ‖boundaryAmplitude a t‖ ≤ amplitudeSupremum a :=
  le_csSup (amplitudeSupremum_bddAbove a ha) ⟨t, ht, rfl⟩

theorem amplitudeSupremum_nonneg (a : ℝ) (ha : |a| < 1) : 0 ≤ amplitudeSupremum a :=
  (norm_nonneg (boundaryAmplitude a 0)).trans (amplitude_le_supremum a ha 0 ⟨le_rfl, by positivity⟩)

theorem amplitude_deriv_continuous (a : ℝ) (ha : |a| < 1) :
    Continuous (deriv (boundaryAmplitude a)) :=
  (boundaryAmplitude_contDiff a ha).continuous_deriv (by simp)

theorem amplitudeVariation_integrable (a : ℝ) (ha : |a| < 1) :
    IntervalIntegrable (fun t => ‖deriv (boundaryAmplitude a) t‖) volume 0 (2 * Real.pi) :=
  (amplitude_deriv_continuous a ha).norm.intervalIntegrable _ _

theorem amplitudeVariation_nonneg (a : ℝ) : 0 ≤ amplitudeVariation a :=
  intervalIntegral.integral_nonneg_of_forall (by positivity) (fun t => norm_nonneg _)

theorem upperOscillationConstant_pos (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < upperOscillationConstant a := by
  have ha : |a| < 1 := by rwa [abs_of_pos ha0]
  unfold upperOscillationConstant
  apply div_pos _ (by positivity)
  have hc := amplitudeConstant_pos a ha0 ha1
  have hs := amplitudeSupremum_nonneg a ha
  have hv := amplitudeVariation_nonneg a
  positivity

theorem poissonDensityDerivative_continuous (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Continuous (poissonDensityDerivative a) := by
  have he : deriv (poissonDensity a) = poissonDensityDerivative a :=
    funext (fun t => (poissonDensity_hasDerivAt a ha0 ha1 t).deriv)
  rw [← he]
  exact (poissonDensity_contDiff a ha0 ha1).continuous_deriv (by simp)

/-- The general interval estimate applied to the actual Blaschke phase and candidate amplitude. -/
theorem upperCandidate_oscillatory_integral (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (m w : ℝ) (hm : 1 ≤ m) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), boundaryAmplitude a t *
        Complex.exp (Complex.I * ((m * realPhase a t - w * t : ℝ) : ℂ))‖ ≤
      upperOscillationConstant a / Real.sqrt m := by
  have ha : |a| < 1 := by rwa [abs_of_pos ha0]
  have h := oscillatory_integral_bound (A := boundaryAmplitude a) (A' := deriv (boundaryAmplitude a))
    (θ := realPhase a) (θ' := poissonDensity a) (θ'' := poissonDensityDerivative a) (w := w)
    hm (amplitudeConstant_pos a ha0 ha1).le (amplitudeSupremum_nonneg a ha)
    (boundaryAmplitude_contDiff a ha).continuous.continuousOn
    (amplitude_deriv_continuous a ha).continuousOn
    (realPhase_contDiff a ha0.le ha1).continuous.continuousOn
    (poissonDensity_contDiff a ha0.le ha1).continuous.continuousOn
    (poissonDensityDerivative_continuous a ha0.le ha1).continuousOn
    (fun t _ => ((boundaryAmplitude_contDiff a ha).differentiable (by simp) t).hasDerivAt)
    (fun t _ => realPhase_hasDerivAt a ha0.le ha1 t)
    (fun t _ => poissonDensity_hasDerivAt a ha0.le ha1 t)
    (Or.inr (poissonDensity_antitone_first a ha0.le ha1))
    (Or.inl (poissonDensity_monotone_second a ha0.le ha1))
    (amplitude_le_supremum a ha)
    (fun t _ => by simpa only [realPhase_second_deriv a ha0.le ha1] using boundaryAmplitude_control a ha0 ha1 t)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((4 * amplitudeConstant a + 12 * amplitudeSupremum a + amplitudeVariation a) / Real.sqrt m) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by unfold upperOscillationConstant; ring

end LocalCertification.Asymptotic
