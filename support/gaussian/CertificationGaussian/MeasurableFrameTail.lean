import CertificationGaussian.MeasurableFramePolynomial

/-! # Explicit Gaussian tails for actual measurable matrix ensembles

The variance estimate controls the centered second moment. Its
dimension-dependent frame estimate supplies the L2 input of hypercontractivity
and then Markov's inequality, with no unknown L2 norm in the final tail.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CertificationGaussian
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (ν : Measure Ω) [IsProbabilityMeasure ν]
  (B : Ω → Matrix I I ℂ) (hB : AEStronglyMeasurable B ν)
  (hH : ∀ᵐ s ∂ν, (B s).IsHermitian) {K : ℝ} (hK : 0 ≤ K)
  (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
include hB hH hK hbound

theorem measurableQuadraticEnsemble_continuous : Continuous (measurableQuadraticEnsemble ν B) := by
  have he : measurableQuadraticEnsemble ν B = fun x =>
      MvPolynomial.eval x (gaussianFramePolynomial (integralMatrixFrame ν B) 0) := by
    funext x
    simpa only [sub_zero] using measurableQuadraticEnsemble_centered_eq_polynomial ν B hB hH hK hbound 0 x
  rw [he]
  exact MvPolynomial.continuous_eval _

theorem measurableQuadraticEnsemble_centered_second (v : ℝ)
    (htrace : (∫ s, ((B s)^2).trace.re ∂ν) = v) :
    (∫ x, (measurableQuadraticEnsemble ν B x-v)^2 ∂pairedGaussian I) =
      variance (measurableQuadraticEnsemble ν B) (pairedGaussian I) := by
  rw [variance_eq_integral (measurableQuadraticEnsemble_continuous ν B hB hH hK hbound).measurable.aemeasurable,
    measurableQuadraticEnsemble_mean ν B hB hH hK hbound, htrace]

variable (v L : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L^2)
  (htrace : (∫ s, ((B s)^2).trace.re ∂ν) = v)
  (hsecond : integralMatrixSecondMoment ν B =
    ((v / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ))
  (hframe : ‖integralMatrixFrame ν B‖ ≤ L^2 / (Fintype.card I : ℝ))
include hv hvL htrace hsecond hframe

theorem measurableQuadraticEnsemble_centered_eLpNorm_two_le :
    eLpNorm (fun x => measurableQuadraticEnsemble ν B x-v) 2 (pairedGaussian I) ≤
      ENNReal.ofReal (Real.sqrt (8*L^2*v/(Fintype.card I:ℝ))) := by
  have hf : MemLp (fun x => measurableQuadraticEnsemble ν B x-v) 2 (pairedGaussian I) := by
    simpa only [ENNReal.ofReal_ofNat] using
      measurableQuadraticEnsemble_centered_memLp ν B hB hH hK hbound v 2 (by norm_num)
  apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).mp
  rw [eLpNorm_two_toReal_sq hf, Real.sq_sqrt (by positivity),
    measurableQuadraticEnsemble_centered_second ν B hB hH hK hbound v htrace]
  exact measurableQuadraticEnsemble_variance_le_eight ν B hB hH hK hbound v L hv hvL htrace hsecond hframe

theorem measurableQuadraticEnsemble_centered_eLpNorm_explicit (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun x => measurableQuadraticEnsemble ν B x-v) (ENNReal.ofReal p) (pairedGaussian I) ≤
      ENNReal.ofReal (5*(p-1)^2 * Real.sqrt (8*L^2*v/(Fintype.card I:ℝ))) := by
  calc
    _ ≤ ENNReal.ofReal (5*(p-1)^2) *
        eLpNorm (fun x => measurableQuadraticEnsemble ν B x-v) 2 (pairedGaussian I) :=
      measurableQuadraticEnsemble_centered_eLpNorm ν B hB hH hK hbound v p hp
    _ ≤ ENNReal.ofReal (5*(p-1)^2) * ENNReal.ofReal (Real.sqrt (8*L^2*v/(Fintype.card I:ℝ))) := by
      gcongr
      exact measurableQuadraticEnsemble_centered_eLpNorm_two_le ν B hB hH hK hbound v L hv hvL htrace hsecond hframe
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- The actual fixed-frame tail, ready for finite nets; the radius-zero kernel
is included by the same moment and frame hypotheses. -/
theorem measurableQuadraticEnsemble_centered_abs_tail (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht : 0 < t) :
    (pairedGaussian I) {x | t ≤ |measurableQuadraticEnsemble ν B x-v|} ≤
      ENNReal.ofReal ((5*(p-1)^2 * Real.sqrt (8*L^2*v/(Fintype.card I:ℝ))/t)^p) :=
  measure_abs_ge_le_of_eLpNorm_le _ _ (by linarith) (by positivity) ht
    (measurableQuadraticEnsemble_centered_eLpNorm_explicit ν B hB hH hK hbound v L hv hvL htrace hsecond hframe p hp)

end CertificationGaussian
