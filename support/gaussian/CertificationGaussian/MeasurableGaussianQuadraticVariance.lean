import CertificationGaussian.MeasurableQuadraticFrame

/-! # Actual Gaussian variance for arbitrary reference probability ensembles

All product integrability and Fubini hypotheses are derived from the genuine
Gaussian polynomial majorant. Matrix inputs need not commute.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

local instance quadraticVariancePairedGaussianProbability : IsProbabilityMeasure (pairedGaussian I) := by
  unfold pairedGaussian
  infer_instance

def quadraticEnsembleFourthTrace (A B : Matrix I I ℂ) : ℝ :=
  (A^2).trace.re * (B^2).trace.re + 2 * (A*B).trace.re ^ 2 +
    2 * (A*B*A*B).trace.re + 4 * (A^2*B^2).trace.re

def quadraticEnsembleCovarianceTrace (A B : Matrix I I ℂ) : ℝ :=
  2 * (A*B).trace.re ^ 2 + 2 * (A*B*A*B).trace.re + 4 * (A^2*B^2).trace.re

theorem measurableQuadraticEnsemble_pair_joint_integrable (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    Integrable (fun p : (Ω × Ω) × (Fin 2 × I → ℝ) =>
      (complexGaussianCenteredQuadratic (B p.1.1) p.2).re ^ 2 *
      (complexGaussianCenteredQuadratic (B p.1.2) p.2).re ^ 2)
      ((ν.prod ν).prod (pairedGaussian I)) := by
  have hc : Continuous (fun p : ((Matrix I I ℂ) × (Matrix I I ℂ)) × (Fin 2 × I → ℝ) =>
      (complexGaussianCenteredQuadratic p.1.1 p.2).re ^ 2 *
      (complexGaussianCenteredQuadratic p.1.2 p.2).re ^ 2) := by
    unfold complexGaussianCenteredQuadratic sphereQuadraticForm Matrix.trace Matrix.diag complexCoordinate
    fun_prop
  have hBM : AEStronglyMeasurable (fun p : Ω × Ω => (B p.1, B p.2)) (ν.prod ν) :=
    hB.comp_fst.prodMk hB.comp_snd
  have hBM' : AEStronglyMeasurable (fun p : (Ω × Ω) × (Fin 2 × I → ℝ) => (B p.1.1, B p.1.2))
      ((ν.prod ν).prod (pairedGaussian I)) := hBM.comp_fst
  have hXM : AEStronglyMeasurable (fun p : (Ω × Ω) × (Fin 2 × I → ℝ) => p.2)
      ((ν.prod ν).prod (pairedGaussian I)) := aestronglyMeasurable_id.comp_snd
  have hG := gaussianCenteredProjector_hs_norm_sq_memLp (I := I)
  have hG4 : Integrable (fun x : Fin 2 × I → ℝ =>
      (‖matrixHilbertSchmidt (gaussianCenteredProjector x)‖ ^ 2)^2) (pairedGaussian I) := by
    simpa only [pow_two, Pi.mul_def] using hG.integrable_mul hG
  apply ((hG4.comp_snd (ν.prod ν)).const_mul (K^4)).mono'
    (hc.comp_aestronglyMeasurable (hBM'.prodMk hXM))
  have hH1 : ∀ᵐ p : (Ω × Ω) × (Fin 2 × I → ℝ) ∂(ν.prod ν).prod (pairedGaussian I),
      (B p.1.1).IsHermitian := Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hH)
  have hH2 : ∀ᵐ p : (Ω × Ω) × (Fin 2 × I → ℝ) ∂(ν.prod ν).prod (pairedGaussian I),
      (B p.1.2).IsHermitian := Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hH)
  have hb1 : ∀ᵐ p : (Ω × Ω) × (Fin 2 × I → ℝ) ∂(ν.prod ν).prod (pairedGaussian I),
      ‖matrixHilbertSchmidt (B p.1.1)‖ ≤ K := Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hbound)
  have hb2 : ∀ᵐ p : (Ω × Ω) × (Fin 2 × I → ℝ) ∂(ν.prod ν).prod (pairedGaussian I),
      ‖matrixHilbertSchmidt (B p.1.2)‖ ≤ K := Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hbound)
  filter_upwards [hH1, hH2, hb1, hb2] with p hp1 hp2 hbp1 hbp2
  have h1 := (complexGaussianCenteredQuadratic_square_le (B p.1.1) hp1 p.2).trans
    (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hK).mpr hbp1) (sq_nonneg _))
  have h2 := (complexGaussianCenteredQuadratic_square_le (B p.1.2) hp2 p.2).trans
    (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hK).mpr hbp2) (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  calc
    _ ≤ (K^2 * ‖matrixHilbertSchmidt (gaussianCenteredProjector p.2)‖ ^ 2) *
        (K^2 * ‖matrixHilbertSchmidt (gaussianCenteredProjector p.2)‖ ^ 2) :=
      mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by ring

theorem measurableQuadraticEnsemble_mean_trace_integrable (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    Integrable (fun s => ((B s)^2).trace.re) ν := by
  apply (measurableQuadraticEnsemble_joint_integrable ν B hB hH hK hbound).integral_prod_left.congr
  filter_upwards [hH] with s hs
  exact complexGaussian_centered_quadratic_real_second (B s) hs

theorem measurableQuadraticEnsemble_fourth_trace_integrable (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    Integrable (fun p : Ω × Ω => quadraticEnsembleFourthTrace (B p.1) (B p.2)) (ν.prod ν) := by
  apply (measurableQuadraticEnsemble_pair_joint_integrable ν B hB hH hK hbound).integral_prod_left.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hH,
    Measure.quasiMeasurePreserving_snd.ae hH] with p hp1 hp2
  exact complexGaussian_centered_quadratic_real_fourth (B p.1) (B p.2) hp1 hp2

theorem measurableQuadraticEnsemble_second (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    (∫ x, measurableQuadraticEnsemble ν B x ^ 2 ∂pairedGaussian I) =
      ∫ p : Ω × Ω, quadraticEnsembleFourthTrace (B p.1) (B p.2) ∂ν.prod ν := by
  have he (x : Fin 2 × I → ℝ) : measurableQuadraticEnsemble ν B x ^ 2 =
      ∫ p : Ω × Ω, (complexGaussianCenteredQuadratic (B p.1) x).re ^ 2 *
        (complexGaussianCenteredQuadratic (B p.2) x).re ^ 2 ∂ν.prod ν := by
    rw [integral_prod_mul (fun s => (complexGaussianCenteredQuadratic (B s) x).re ^ 2)
      (fun s => (complexGaussianCenteredQuadratic (B s) x).re ^ 2)]
    rw [measurableQuadraticEnsemble, pow_two]
  simp_rw [he]
  rw [← integral_integral_swap
    (measurableQuadraticEnsemble_pair_joint_integrable ν B hB hH hK hbound)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hH,
    Measure.quasiMeasurePreserving_snd.ae hH] with p hp1 hp2
  exact complexGaussian_centered_quadratic_real_fourth (B p.1) (B p.2) hp1 hp2

/-- The genuine noncommuting covariance integrated over any reference probability. -/
theorem measurableQuadraticEnsemble_variance (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    variance (measurableQuadraticEnsemble ν B) (pairedGaussian I) =
      ∫ p : Ω × Ω, quadraticEnsembleCovarianceTrace (B p.1) (B p.2) ∂ν.prod ν := by
  rw [variance_eq_sub (measurableQuadraticEnsemble_memLp ν B hB hH hK hbound)]
  change (∫ x, measurableQuadraticEnsemble ν B x ^ 2 ∂pairedGaussian I) -
    (∫ x, measurableQuadraticEnsemble ν B x ∂pairedGaussian I)^2 = _
  rw [measurableQuadraticEnsemble_second ν B hB hH hK hbound,
    measurableQuadraticEnsemble_mean ν B hB hH hK hbound]
  have hm := measurableQuadraticEnsemble_mean_trace_integrable ν B hB hH hK hbound
  have he : (∫ s, ((B s)^2).trace.re ∂ν)^2 =
      ∫ p : Ω × Ω, ((B p.1)^2).trace.re * ((B p.2)^2).trace.re ∂ν.prod ν := by
    rw [integral_prod_mul (fun s => ((B s)^2).trace.re) (fun s => ((B s)^2).trace.re), pow_two]
  rw [he, ← integral_sub (measurableQuadraticEnsemble_fourth_trace_integrable ν B hB hH hK hbound)
    (hm.mul_prod hm)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    unfold quadraticEnsembleFourthTrace quadraticEnsembleCovarianceTrace
    ring

end CertificationGaussian
