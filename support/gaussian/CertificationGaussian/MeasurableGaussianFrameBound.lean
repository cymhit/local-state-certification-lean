import CertificationGaussian.MeasurableGaussianQuadraticVariance

/-! # Actual frame control for arbitrary measurable Gaussian ensembles

All operators and matrix moments below are Bochner integrals. Bounded measurable
Hilbert-Schmidt support supplies the integrability of continuous matrix expressions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

private def hsDecode (x : EuclideanSpace ℂ (I × I)) : Matrix I I ℂ := fun i j => x (i,j)

omit [Fintype I] [DecidableEq I] in
private theorem hsDecode_continuous : Continuous (hsDecode (I := I)) := by
  unfold hsDecode
  fun_prop

omit [DecidableEq I] in
/-- A continuous matrix observable is integrable on bounded HS support. -/
theorem measurableMatrix_continuous_integrable {F : Type*} [NormedAddCommGroup F]
    (B : Ω → Matrix I I ℂ) (hB : AEStronglyMeasurable B ν)
    {K : ℝ} (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
    (f : Matrix I I ℂ → F) (hf : Continuous f) : Integrable (fun s => f (B s)) ν := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : EuclideanSpace ℂ (I × I)) K).image
    (hf.comp hsDecode_continuous)).isBounded.exists_norm_le
  apply (integrable_const M).mono' (hf.comp_aestronglyMeasurable hB)
  filter_upwards [hbound] with s hs
  exact hM _ ⟨matrixHilbertSchmidt (B s), by simpa only [Metric.mem_closedBall, dist_zero_right] using hs, rfl⟩

omit [DecidableEq I] in
/-- The same derived integrability for two independently drawn ensemble outcomes. -/
theorem measurableMatrix_pair_continuous_integrable {F : Type*} [NormedAddCommGroup F]
    (B : Ω → Matrix I I ℂ) (hB : AEStronglyMeasurable B ν)
    {K : ℝ} (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
    (f : (Matrix I I ℂ) × (Matrix I I ℂ) → F) (hf : Continuous f) :
    Integrable (fun p : Ω × Ω => f (B p.1, B p.2)) (ν.prod ν) := by
  have hc : Continuous (fun p : (EuclideanSpace ℂ (I × I)) × (EuclideanSpace ℂ (I × I)) =>
      f (hsDecode p.1, hsDecode p.2)) :=
    hf.comp ((hsDecode_continuous.comp continuous_fst).prodMk (hsDecode_continuous.comp continuous_snd))
  obtain ⟨M, hM⟩ := (((isCompact_closedBall (0 : EuclideanSpace ℂ (I × I)) K).prod
    (isCompact_closedBall (0 : EuclideanSpace ℂ (I × I)) K)).image hc).isBounded.exists_norm_le
  apply (integrable_const M).mono'
    (hf.comp_aestronglyMeasurable (hB.comp_fst.prodMk hB.comp_snd))
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbound,
    Measure.quasiMeasurePreserving_snd.ae hbound] with p hp1 hp2
  exact hM _ ⟨(matrixHilbertSchmidt (B p.1), matrixHilbertSchmidt (B p.2)),
    ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hp1,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using hp2⟩, rfl⟩

def integralMatrixFrame (B : Ω → Matrix I I ℂ) :=
  integralHilbertFrame ν (fun s => matrixHilbertSchmidt (B s))

def integralMatrixSecondMoment (B : Ω → Matrix I I ℂ) : Matrix I I ℂ := ∫ s, (B s)^2 ∂ν

private def realTraceProduct (A : Matrix I I ℂ) : (Matrix I I ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (A * M).trace.re
      map_add' := by intro M N; simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by intro c M; simp [Matrix.trace_smul] }

theorem integralMatrixSecondMoment_trace_square (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν)
    {K : ℝ} (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    (∫ p : Ω × Ω, ((B p.1)^2 * (B p.2)^2).trace.re ∂ν.prod ν) =
      ((integralMatrixSecondMoment ν B)^2).trace.re := by
  have hsq := measurableMatrix_continuous_integrable ν B hB hbound (fun A => A^2) (by fun_prop)
  have hpair := measurableMatrix_pair_continuous_integrable ν B hB hbound
    (fun p => (p.1^2 * p.2^2).trace.re) (by unfold Matrix.trace Matrix.diag; fun_prop)
  rw [integral_prod _ hpair]
  have hi (s : Ω) : (∫ t, ((B s)^2 * (B t)^2).trace.re ∂ν) =
      ((B s)^2 * integralMatrixSecondMoment ν B).trace.re :=
    (realTraceProduct ((B s)^2)).integral_comp_comm hsq
  simp_rw [hi, Matrix.trace_mul_comm ((B _)^2) (integralMatrixSecondMoment ν B)]
  change (∫ s, realTraceProduct (integralMatrixSecondMoment ν B) ((B s)^2) ∂ν) = _
  rw [(realTraceProduct (integralMatrixSecondMoment ν B)).integral_comp_comm hsq]
  change (integralMatrixSecondMoment ν B * integralMatrixSecondMoment ν B).trace.re = _
  rw [pow_two]

/-- The actual frame second moment is bounded by its operator norm times its trace. -/
theorem integralMatrixFrame_pairing_bound (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    (∫ p : Ω × Ω, (B p.1 * B p.2).trace.re ^ 2 ∂ν.prod ν) ≤
      ‖integralMatrixFrame ν B‖ * (∫ s, ((B s)^2).trace.re ∂ν) := by
  have hV : AEStronglyMeasurable (fun s => matrixHilbertSchmidt (B s)) ν :=
    (show Continuous (matrixHilbertSchmidt (I := I)) by unfold matrixHilbertSchmidt; fun_prop).comp_aestronglyMeasurable hB
  have hp := measurableMatrix_pair_continuous_integrable ν B hB hbound
    (fun p => (p.1 * p.2).trace.re ^ 2) (by unfold Matrix.trace Matrix.diag; fun_prop)
  have hm := measurableQuadraticEnsemble_mean_trace_integrable ν B hB hH hK hbound
  calc
    _ = ∫ s, ∫ t, (B s * B t).trace.re ^ 2 ∂ν ∂ν := integral_prod _ hp
    _ ≤ ∫ s, ‖integralMatrixFrame ν B‖ * ((B s)^2).trace.re ∂ν := by
      apply integral_mono_ae hp.integral_prod_left (hm.const_mul _)
      filter_upwards [hH] with s hs
      have he : (∫ t, (B s * B t).trace.re ^ 2 ∂ν) =
          inner ℝ (integralMatrixFrame ν B (matrixHilbertSchmidt (B s))) (matrixHilbertSchmidt (B s)) := by
        rw [integralMatrixFrame, integralHilbertFrame_inner ν _ hV hK hbound]
        apply integral_congr_ae
        filter_upwards [hH] with t ht
        rw [matrixHilbertSchmidt_inner _ _ ht, Matrix.trace_mul_comm (B t) (B s), pow_two]
      rw [he, ← matrixHilbertSchmidt_norm_sq _ hs]
      calc
        _ ≤ ‖integralMatrixFrame ν B (matrixHilbertSchmidt (B s))‖ * ‖matrixHilbertSchmidt (B s)‖ :=
          real_inner_le_norm _ _
        _ ≤ (‖integralMatrixFrame ν B‖ * ‖matrixHilbertSchmidt (B s)‖) * ‖matrixHilbertSchmidt (B s)‖ :=
          mul_le_mul_of_nonneg_right ((integralMatrixFrame ν B).le_opNorm _) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

/-- Frame contraction bounds the Gaussian quadratic variance for arbitrary measurable outcomes. -/
theorem measurableQuadraticEnsemble_variance_le (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    variance (measurableQuadraticEnsemble ν B) (pairedGaussian I) ≤
      2 * ‖integralMatrixFrame ν B‖ * (∫ s, ((B s)^2).trace.re ∂ν) +
        6 * ((integralMatrixSecondMoment ν B)^2).trace.re := by
  have hi (f : (Matrix I I ℂ) × (Matrix I I ℂ) → ℝ) (hf : Continuous f) :=
    measurableMatrix_pair_continuous_integrable ν B hB hbound f hf
  have hcov := hi (fun p => quadraticEnsembleCovarianceTrace p.1 p.2)
    (by unfold quadraticEnsembleCovarianceTrace Matrix.trace Matrix.diag; fun_prop)
  have hp := hi (fun p => (p.1 * p.2).trace.re ^ 2) (by unfold Matrix.trace Matrix.diag; fun_prop)
  have hsq := hi (fun p => (p.1^2 * p.2^2).trace.re) (by unfold Matrix.trace Matrix.diag; fun_prop)
  have hbound' : variance (measurableQuadraticEnsemble ν B) (pairedGaussian I) ≤
      ∫ p : Ω × Ω, 2 * (B p.1 * B p.2).trace.re ^ 2 +
        6 * ((B p.1)^2 * (B p.2)^2).trace.re ∂ν.prod ν := by
    rw [measurableQuadraticEnsemble_variance ν B hB hH hK hbound]
    apply integral_mono_ae hcov ((hp.const_mul 2).add (hsq.const_mul 6))
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hH,
      Measure.quasiMeasurePreserving_snd.ae hH] with p hp1 hp2
    have hcycle : (B p.1 * B p.2 * B p.1 * B p.2).trace.re ≤
        ((B p.1)^2 * (B p.2)^2).trace.re := by
      apply (Complex.re_le_norm _).trans
      simpa only [show 2 - 1 = (1 : ℕ) from rfl, pow_one] using
        hermitian_trace_sandwich (B p.1) (B p.2) hp1 hp2
          (k := 2) (l := 1) (by decide) (by omega)
    unfold quadraticEnsembleCovarianceTrace
    dsimp only [Pi.add_apply]
    linarith
  rw [integral_add (hp.const_mul 2) (hsq.const_mul 6), integral_const_mul, integral_const_mul,
    integralMatrixSecondMoment_trace_square ν B hB hbound] at hbound'
  have hpair := integralMatrixFrame_pairing_bound ν B hB hH hK hbound
  nlinarith

/-- The frame contraction and matrix moment bounds imply the scalar variance bound. -/
theorem measurableQuadraticEnsemble_variance_le_scalar (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
    (v L : ℝ) (hv : 0 ≤ v)
    (htrace : (∫ s, ((B s)^2).trace.re ∂ν) = v)
    (hsecond : integralMatrixSecondMoment ν B =
      ((v / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ))
    (hframe : ‖integralMatrixFrame ν B‖ ≤ L^2 / (Fintype.card I : ℝ)) :
    variance (measurableQuadraticEnsemble ν B) (pairedGaussian I) ≤
      (2 * L^2 * v + 6 * v^2) / (Fintype.card I : ℝ) := by
  have h := measurableQuadraticEnsemble_variance_le ν B hB hH hK hbound
  rw [htrace, hsecond] at h
  have hs : ((((v / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ))^2).trace.re =
      v^2 / (Fintype.card I : ℝ) := by
    by_cases hd : (Fintype.card I : ℝ) = 0
    · simp [hd]
    · simp only [pow_two, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
        mul_zero, sub_zero]
      field_simp
  rw [hs] at h
  calc
    _ ≤ 2 * ‖integralMatrixFrame ν B‖ * v + 6 * (v^2 / (Fintype.card I : ℝ)) := h
    _ ≤ 2 * (L^2 / (Fintype.card I : ℝ)) * v + 6 * (v^2 / (Fintype.card I : ℝ)) := by gcongr
    _ = _ := by ring

theorem measurableQuadraticEnsemble_variance_le_eight (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
    (v L : ℝ) (hv : 0 ≤ v) (hvL : v ≤ L^2)
    (htrace : (∫ s, ((B s)^2).trace.re ∂ν) = v)
    (hsecond : integralMatrixSecondMoment ν B =
      ((v / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ))
    (hframe : ‖integralMatrixFrame ν B‖ ≤ L^2 / (Fintype.card I : ℝ)) :
    variance (measurableQuadraticEnsemble ν B) (pairedGaussian I) ≤
      8 * L^2 * v / (Fintype.card I : ℝ) := by
  apply (measurableQuadraticEnsemble_variance_le_scalar ν B hB hH hK hbound v L hv htrace hsecond hframe).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hvL hv]

/-- Arbitrary measurable rank-one POVMs include the zero-radius branch. -/
theorem measurableRankOneGaussian_zeroRadius_variance (u : Ω → EuclideanSpace ℂ I)
    (hu : AEStronglyMeasurable u ν) (hunit : ∀ᵐ s ∂ν, ‖u s‖ = 1)
    (hmean : (∫ s, vectorRankOne (u s) (u s) ∂ν) =
      (((1 : ℝ) / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ)) :
    variance (measurableQuadraticEnsemble ν (fun s => vectorRankOne (u s) (u s)))
      (pairedGaussian I) ≤ 8 / (Fintype.card I : ℝ) := by
  let B := fun s => vectorRankOne (u s) (u s)
  have hB : AEStronglyMeasurable B ν :=
    (show Continuous (fun v : EuclideanSpace ℂ I => vectorRankOne v v) by unfold vectorRankOne; fun_prop).comp_aestronglyMeasurable hu
  have hH : ∀ᵐ s ∂ν, (B s).IsHermitian := Filter.Eventually.of_forall fun s => vectorRankOne_self_hermitian _
  have hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ 1 := by
    filter_upwards [hunit] with s hs
    have hn : ‖matrixHilbertSchmidt (B s)‖ ^ 2 = 1 := by
      rw [matrixHilbertSchmidt_norm_sq _ (vectorRankOne_self_hermitian _),
        vectorRankOne_self_sq _ hs, vectorRankOne_self_trace _ hs, Complex.one_re]
    nlinarith [norm_nonneg (matrixHilbertSchmidt (B s))]
  have htrace : (∫ s, ((B s)^2).trace.re ∂ν) = 1 := by
    calc
      _ = ∫ _ : Ω, (1 : ℝ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hunit] with s hs
        rw [vectorRankOne_self_sq _ hs, vectorRankOne_self_trace _ hs, Complex.one_re]
      _ = 1 := by simp
  have hsecond : integralMatrixSecondMoment ν B =
      (((1 : ℝ) / (Fintype.card I : ℝ) : ℝ) : ℂ) • (1 : Matrix I I ℂ) := by
    rw [integralMatrixSecondMoment, ← hmean]
    apply integral_congr_ae
    filter_upwards [hunit] with s hs
    exact vectorRankOne_self_sq _ hs
  have hf := measurableRankOneFrame_norm_le ν u hu hunit
    (by positivity : 0 ≤ (1 : ℝ) / (Fintype.card I : ℝ)) hmean
  have h := measurableQuadraticEnsemble_variance_le_eight ν B hB hH (by norm_num : (0 : ℝ) ≤ 1)
    hbound 1 1 (by norm_num) (by norm_num) htrace hsecond
    (by simpa only [one_pow, integralMatrixFrame, B] using hf)
  simpa only [one_pow, mul_one] using h

end CertificationGaussian
