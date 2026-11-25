import CertificationGaussian.FiniteRankOneFrame

/-! # Frames of arbitrary measurable probability ensembles

The outcome space is arbitrary. Frames are genuine Bochner integrals, and
their integrability is derived from measurable bounded vectors.
-/

noncomputable section
open MeasureTheory Matrix Finset
open scoped BigOperators
namespace CertificationGaussian

section HilbertFrame
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

/-- The actual operator-valued frame integral for a general outcome space. -/
def integralHilbertFrame (V : Ω → E) : E →L[ℝ] E :=
  ∫ s, InnerProductSpace.rankOne ℝ (V s) (V s) ∂ν

omit [CompleteSpace E] in
theorem integralHilbertFrame_integrable (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) :
    Integrable (fun s => InnerProductSpace.rankOne ℝ (V s) (V s)) ν := by
  have hc : Continuous (fun x : E => InnerProductSpace.rankOne ℝ x x) :=
    (InnerProductSpace.rankOne ℝ).continuous.clm_apply continuous_id
  apply (integrable_const (K^2)).mono' (hc.comp_aestronglyMeasurable hV)
  filter_upwards [hbound] with s hs
  rw [InnerProductSpace.norm_rankOne, ← pow_two]
  exact (sq_le_sq₀ (norm_nonneg _) hK).mpr hs

omit [CompleteSpace E] in
theorem integralHilbertFrame_pair_integrable (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (x y : E) :
    Integrable (fun s => inner ℝ (V s) x * inner ℝ (V s) y) ν := by
  have h := Integrable.const_inner (𝕜 := ℝ) y
    ((ContinuousLinearMap.apply ℝ E x).integrable_comp
      (integralHilbertFrame_integrable ν V hV hK hbound))
  simpa only [ContinuousLinearMap.apply_apply, InnerProductSpace.rankOne_apply, real_inner_smul_right,
    real_inner_comm y, mul_comm] using h

theorem integralHilbertFrame_inner (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (x y : E) :
    inner ℝ (integralHilbertFrame ν V x) y =
      ∫ s, inner ℝ (V s) x * inner ℝ (V s) y ∂ν := by
  have hF := integralHilbertFrame_integrable ν V hV hK hbound
  have hFx : Integrable (fun s => InnerProductSpace.rankOne ℝ (V s) (V s) x) ν := by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ E x).integrable_comp hF
  rw [integralHilbertFrame, ContinuousLinearMap.integral_apply hF x, real_inner_comm,
    ← integral_inner (𝕜 := ℝ) hFx]
  simp only [InnerProductSpace.rankOne_apply, real_inner_smul_right,
    real_inner_comm y, mul_comm]

/-- The actual quadratic-form bound controls the Bochner frame operator norm. -/
theorem integralHilbertFrame_norm_le (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K c : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (hc : 0 ≤ c)
    (hquad : ∀ x, (∫ s, inner ℝ (V s) x ^ 2 ∂ν) ≤ c * ‖x‖ ^ 2) :
    ‖integralHilbertFrame ν V‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hc
  intro x y hx hy
  change inner ℝ (integralHilbertFrame ν V x) y ≤ c
  rw [integralHilbertFrame_inner ν V hV hK hbound]
  have hi (x : E) : Integrable (fun s => inner ℝ (V s) x ^ 2) ν := by
    simpa only [pow_two] using integralHilbertFrame_pair_integrable ν V hV hK hbound x x
  have hxy := integral_mono
    (integralHilbertFrame_pair_integrable ν V hV hK hbound x y)
    (((hi x).add (hi y)).div_const 2)
    (show ∀ s, inner ℝ (V s) x * inner ℝ (V s) y ≤
      (inner ℝ (V s) x ^ 2 + inner ℝ (V s) y ^ 2) / 2 from
      fun s => by nlinarith [sq_nonneg (inner ℝ (V s) x - inner ℝ (V s) y)])
  rw [integral_div] at hxy
  simp only [Pi.add_apply] at hxy
  rw [integral_add (hi x) (hi y)] at hxy
  have hqx := hquad x
  have hqy := hquad y
  rw [hx, one_pow, mul_one] at hqx
  rw [hy, one_pow, mul_one] at hqy
  linarith

end HilbertFrame

section RankOne
open scoped Matrix.Norms.L2Operator
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

private def matrixRealTracePairing (A : Matrix I I ℂ) : (Matrix I I ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (A * M).trace.re
      map_add' := by intro M N; simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by intro c M; simp [Matrix.trace_smul] }

theorem measurableRankOne_integrable (u : Ω → EuclideanSpace ℂ I)
    (hu : AEStronglyMeasurable u ν) (hunit : ∀ᵐ s ∂ν, ‖u s‖ = 1) :
    Integrable (fun s => vectorRankOne (u s) (u s)) ν := by
  have hc : Continuous (fun v : EuclideanSpace ℂ I => vectorRankOne v v) := by
    unfold vectorRankOne
    fun_prop
  obtain ⟨K, hK⟩ := ((isCompact_sphere (0 : EuclideanSpace ℂ I) 1).image hc).isBounded.exists_norm_le
  apply (integrable_const K).mono' (hc.comp_aestronglyMeasurable hu)
  filter_upwards [hunit] with s hs
  exact hK _ ⟨u s, by simpa only [Metric.mem_sphere, dist_zero_right] using hs, rfl⟩

/-- Arbitrary measurable outcomes: the first matrix moment controls the actual HS frame. -/
theorem measurableRankOneFrame_norm_le (u : Ω → EuclideanSpace ℂ I)
    (hu : AEStronglyMeasurable u ν) (hunit : ∀ᵐ s ∂ν, ‖u s‖ = 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hmean : (∫ s, vectorRankOne (u s) (u s) ∂ν) =
      (c : ℂ) • (1 : Matrix I I ℂ)) :
    ‖integralHilbertFrame ν (fun s => matrixHilbertSchmidt (vectorRankOne (u s) (u s)))‖ ≤ c := by
  let V := fun s => matrixHilbertSchmidt (vectorRankOne (u s) (u s))
  have hcont : Continuous (fun v : EuclideanSpace ℂ I => matrixHilbertSchmidt (vectorRankOne v v)) := by
    unfold matrixHilbertSchmidt vectorRankOne
    fun_prop
  have hV : AEStronglyMeasurable V ν := hcont.comp_aestronglyMeasurable hu
  have hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ 1 := by
    filter_upwards [hunit] with s hs
    have hn : ‖V s‖ ^ 2 = 1 := by
      dsimp only [V]
      rw [matrixHilbertSchmidt_norm_sq _ (vectorRankOne_self_hermitian _),
        vectorRankOne_self_sq _ hs, vectorRankOne_self_trace _ hs, Complex.one_re]
    nlinarith [norm_nonneg (V s)]
  apply integralHilbertFrame_norm_le ν V hV (by norm_num : (0 : ℝ) ≤ 1) hbound hc
  intro x
  let A : Matrix I I ℂ := fun i j => x (i,j)
  have hx : matrixHilbertSchmidt A = x := rfl
  have hP := measurableRankOne_integrable ν u hu hunit
  have hR : Integrable (fun s => (A.conjTranspose * A * vectorRankOne (u s) (u s)).trace.re) ν :=
    (matrixRealTracePairing (A.conjTranspose * A)).integrable_comp hP
  have hL : Integrable (fun s => inner ℝ (V s) x ^ 2) ν := by
    simpa only [pow_two] using integralHilbertFrame_pair_integrable ν V hV
      (by norm_num : (0 : ℝ) ≤ 1) hbound x x
  calc
    _ ≤ ∫ s, (A.conjTranspose * A * vectorRankOne (u s) (u s)).trace.re ∂ν := by
      apply integral_mono_ae hL hR
      filter_upwards [hunit] with s hs
      dsimp only [V]
      rw [← hx, matrixHilbertSchmidt_inner _ A (vectorRankOne_self_hermitian _),
        Matrix.trace_mul_comm (vectorRankOne (u s) (u s)) A]
      exact vectorRankOne_trace_sq_le A (u s) hs
    _ = c * ‖x‖ ^ 2 := by
      have hm := (matrixRealTracePairing (A.conjTranspose * A)).integral_comp_comm (μ := ν) hP
      change (∫ s, (A.conjTranspose * A * vectorRankOne (u s) (u s)).trace.re ∂ν) =
        (A.conjTranspose * A * (∫ s, vectorRankOne (u s) (u s) ∂ν)).trace.re at hm
      rw [hmean] at hm
      simpa only [Matrix.mul_smul, mul_one, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        matrixHilbertSchmidt_star_square, hx] using hm

end RankOne

section GaussianEnsemble
open scoped Matrix.Norms.L2Operator
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

/-- The genuine centered Gaussian rank-one matrix zz†-I. -/
def gaussianCenteredProjector (x : Fin 2 × I → ℝ) : Matrix I I ℂ :=
  vectorRankOne (WithLp.toLp 2 (complexCoordinate x)) (WithLp.toLp 2 (complexCoordinate x)) - 1

omit [Fintype I] in
theorem gaussianCenteredProjector_hermitian (x : Fin 2 × I → ℝ) :
    (gaussianCenteredProjector x).IsHermitian :=
  (vectorRankOne_self_hermitian _).sub Matrix.isHermitian_one

theorem complexGaussianCenteredQuadratic_one_re (x : Fin 2 × I → ℝ) :
    (complexGaussianCenteredQuadratic (1 : Matrix I I ℂ) x).re =
      ‖WithLp.toLp 2 (complexCoordinate x)‖ ^ 2 - (Fintype.card I : ℝ) := by
  rw [complexGaussianCenteredQuadratic, sphereQuadraticForm_eq_inner, map_one]
  simp [inner_self_eq_norm_sq_to_K, pow_two, Matrix.trace_one]

theorem gaussianCenteredProjector_hs_norm_sq (x : Fin 2 × I → ℝ) :
    ‖matrixHilbertSchmidt (gaussianCenteredProjector x)‖ ^ 2 =
      (complexGaussianCenteredQuadratic (1 : Matrix I I ℂ) x).re ^ 2 +
        2 * ((Fintype.card I : ℝ) - 1) *
          (complexGaussianCenteredQuadratic (1 : Matrix I I ℂ) x).re +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) := by
  let z := WithLp.toLp 2 (complexCoordinate x)
  have hinner : inner ℂ z z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (Complex.ofReal_pow ‖z‖ 2).symm
  have he : (gaussianCenteredProjector x)^2 =
      vectorRankOne z z * vectorRankOne z z - vectorRankOne z z - vectorRankOne z z + 1 := by
    dsimp only [gaussianCenteredProjector, z]
    noncomm_ring
  rw [matrixHilbertSchmidt_norm_sq _ (gaussianCenteredProjector_hermitian x), he,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, vectorRankOne_mul,
    Matrix.trace_smul, vectorRankOne_trace, hinner,
    complexGaussianCenteredQuadratic_one_re]
  simp only [Matrix.trace_one, Complex.add_re, Complex.sub_re, smul_eq_mul,
    pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.natCast_re]
  dsimp only [z]
  ring

theorem gaussianCenteredProjector_hs_norm_sq_memLp :
    MemLp (fun x : Fin 2 × I → ℝ => ‖matrixHilbertSchmidt (gaussianCenteredProjector x)‖ ^ 2)
      2 (pairedGaussian I) := by
  let : IsProbabilityMeasure (pairedGaussian I) := by unfold pairedGaussian; infer_instance
  have hq : MemLp (fun x : Fin 2 × I → ℝ => (complexGaussianCenteredQuadratic (1 : Matrix I I ℂ) x).re)
      2 (pairedGaussian I) :=
    (complexGaussianCenteredQuadratic_memLp (1 : Matrix I I ℂ) 2 (by norm_num)).re
  have hq2 := complexGaussianCenteredQuadratic_real_square_memLp (1 : Matrix I I ℂ) Matrix.isHermitian_one
  have h := (hq2.add (hq.const_mul (2 * ((Fintype.card I : ℝ) - 1)))).add
    (memLp_const ((Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1)))
  have he : (fun x : Fin 2 × I → ℝ => ‖matrixHilbertSchmidt (gaussianCenteredProjector x)‖ ^ 2) =
      ((fun x => (complexGaussianCenteredQuadratic (1 : Matrix I I ℂ) x).re ^ 2) +
        (fun x => 2 * ((Fintype.card I : ℝ) - 1) *
          (complexGaussianCenteredQuadratic (1 : Matrix I I ℂ) x).re) +
        (fun _ => (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1))) := by
    funext x
    exact gaussianCenteredProjector_hs_norm_sq x
  rw [he]
  exact h

theorem complexGaussianCenteredQuadratic_eq_hs_inner (B : Matrix I I ℂ)
    (hB : B.IsHermitian) (x : Fin 2 × I → ℝ) :
    (complexGaussianCenteredQuadratic B x).re =
      inner ℝ (matrixHilbertSchmidt B) (matrixHilbertSchmidt (gaussianCenteredProjector x)) := by
  rw [matrixHilbertSchmidt_inner B _ hB]
  simp only [gaussianCenteredProjector, Matrix.mul_sub, mul_one, Matrix.trace_sub,
    vectorRankOne_trace_pairing, complexGaussianCenteredQuadratic, Complex.sub_re]

/-- The actual quadratic ensemble observable for an arbitrary reference probability. -/
def measurableQuadraticEnsemble (B : Ω → Matrix I I ℂ) (x : Fin 2 × I → ℝ) : ℝ :=
  ∫ s, (complexGaussianCenteredQuadratic (B s) x).re ^ 2 ∂ν

theorem measurableQuadraticEnsemble_integrable (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
    (x : Fin 2 × I → ℝ) :
    Integrable (fun s => (complexGaussianCenteredQuadratic (B s) x).re ^ 2) ν := by
  have hcont : Continuous (matrixHilbertSchmidt : Matrix I I ℂ → EuclideanSpace ℂ (I × I)) := by
    unfold matrixHilbertSchmidt
    fun_prop
  have hV := hcont.comp_aestronglyMeasurable hB
  have hi := integralHilbertFrame_pair_integrable ν (fun s => matrixHilbertSchmidt (B s)) hV
    hK hbound (matrixHilbertSchmidt (gaussianCenteredProjector x))
      (matrixHilbertSchmidt (gaussianCenteredProjector x))
  apply hi.congr
  filter_upwards [hH] with s hs
  rw [complexGaussianCenteredQuadratic_eq_hs_inner _ hs, pow_two]

/-- The exact arbitrary-outcome functional depends only on its genuine HS frame. -/
theorem measurableQuadraticEnsemble_eq_frame (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
    (x : Fin 2 × I → ℝ) :
    measurableQuadraticEnsemble ν B x =
      inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
        (integralHilbertFrame ν (fun s => matrixHilbertSchmidt (B s))
          (matrixHilbertSchmidt (gaussianCenteredProjector x))) := by
  have hcont : Continuous (matrixHilbertSchmidt : Matrix I I ℂ → EuclideanSpace ℂ (I × I)) := by
    unfold matrixHilbertSchmidt
    fun_prop
  rw [real_inner_comm, integralHilbertFrame_inner ν _ (hcont.comp_aestronglyMeasurable hB) hK hbound]
  apply integral_congr_ae
  filter_upwards [hH] with s hs
  rw [complexGaussianCenteredQuadratic_eq_hs_inner _ hs, pow_two]

/-- The arbitrary-outcome ensemble is genuinely L² under the actual paired Gaussian. -/
theorem measurableQuadraticEnsemble_memLp (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    MemLp (measurableQuadraticEnsemble ν B) 2 (pairedGaussian I) := by
  let T := integralHilbertFrame ν (fun s => matrixHilbertSchmidt (B s))
  let G := fun x : Fin 2 × I → ℝ => matrixHilbertSchmidt (gaussianCenteredProjector x)
  have hcont : Continuous G := by
    unfold G matrixHilbertSchmidt gaussianCenteredProjector vectorRankOne complexCoordinate
    fun_prop
  have he : measurableQuadraticEnsemble ν B = fun x => inner ℝ (G x) (T (G x)) := by
    funext x
    exact measurableQuadraticEnsemble_eq_frame ν B hB hH hK hbound x
  rw [he]
  have hq : AEStronglyMeasurable (fun x => inner ℝ (G x) (T (G x))) (pairedGaussian I) :=
    (hcont.inner (T.continuous.comp hcont)).aestronglyMeasurable
  apply (gaussianCenteredProjector_hs_norm_sq_memLp (I := I)).const_mul ‖T‖ |>.mono' hq
  exact Filter.Eventually.of_forall fun x => by
    calc
      ‖inner ℝ (G x) (T (G x))‖ ≤ ‖G x‖ * ‖T (G x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖G x‖ * (‖T‖ * ‖G x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring

theorem complexGaussianCenteredQuadratic_square_le (B : Matrix I I ℂ)
    (hB : B.IsHermitian) (x : Fin 2 × I → ℝ) :
    (complexGaussianCenteredQuadratic B x).re ^ 2 ≤
      ‖matrixHilbertSchmidt B‖ ^ 2 * ‖matrixHilbertSchmidt (gaussianCenteredProjector x)‖ ^ 2 := by
  rw [complexGaussianCenteredQuadratic_eq_hs_inner _ hB]
  have h := norm_inner_le_norm (𝕜 := ℝ) (matrixHilbertSchmidt B)
    (matrixHilbertSchmidt (gaussianCenteredProjector x))
  rw [Real.norm_eq_abs] at h
  simpa only [sq_abs, mul_pow] using
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h

theorem measurableQuadraticEnsemble_joint_integrable (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    Integrable (fun p : Ω × (Fin 2 × I → ℝ) =>
      (complexGaussianCenteredQuadratic (B p.1) p.2).re ^ 2) (ν.prod (pairedGaussian I)) := by
  let : IsProbabilityMeasure (pairedGaussian I) := by unfold pairedGaussian; infer_instance
  have hc : Continuous (fun p : (Matrix I I ℂ) × (Fin 2 × I → ℝ) =>
      (complexGaussianCenteredQuadratic p.1 p.2).re ^ 2) := by
    unfold complexGaussianCenteredQuadratic sphereQuadraticForm Matrix.trace Matrix.diag complexCoordinate
    fun_prop
  have hBM : AEStronglyMeasurable (fun p : Ω × (Fin 2 × I → ℝ) => B p.1)
      (ν.prod (pairedGaussian I)) := hB.comp_fst
  have hXM : AEStronglyMeasurable (fun p : Ω × (Fin 2 × I → ℝ) => p.2)
      (ν.prod (pairedGaussian I)) := aestronglyMeasurable_id.comp_snd
  have hmeas := hc.comp_aestronglyMeasurable (hBM.prodMk hXM)
  have hG := (gaussianCenteredProjector_hs_norm_sq_memLp (I := I)).integrable (by norm_num)
  apply ((hG.comp_snd ν).const_mul (K^2)).mono' hmeas
  have hHp : ∀ᵐ p : Ω × (Fin 2 × I → ℝ) ∂ν.prod (pairedGaussian I), (B p.1).IsHermitian :=
    Measure.quasiMeasurePreserving_fst.ae hH
  have hbp : ∀ᵐ p : Ω × (Fin 2 × I → ℝ) ∂ν.prod (pairedGaussian I),
      ‖matrixHilbertSchmidt (B p.1)‖ ≤ K := Measure.quasiMeasurePreserving_fst.ae hbound
  filter_upwards [hHp, hbp] with p hp hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (complexGaussianCenteredQuadratic_square_le (B p.1) hp p.2).trans
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hK).mpr hb) (sq_nonneg _)

/-- Actual Gaussian expectation for arbitrary measurable reference probabilities, with Fubini justified. -/
theorem measurableQuadraticEnsemble_mean (B : Ω → Matrix I I ℂ)
    (hB : AEStronglyMeasurable B ν) (hH : ∀ᵐ s ∂ν, (B s).IsHermitian)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) :
    (∫ x, measurableQuadraticEnsemble ν B x ∂pairedGaussian I) =
      ∫ s, ((B s)^2).trace.re ∂ν := by
  let : IsProbabilityMeasure (pairedGaussian I) := by unfold pairedGaussian; infer_instance
  unfold measurableQuadraticEnsemble
  rw [← integral_integral_swap (measurableQuadraticEnsemble_joint_integrable ν B hB hH hK hbound)]
  apply integral_congr_ae
  filter_upwards [hH] with s hs
  exact complexGaussian_centered_quadratic_real_second (B s) hs

end GaussianEnsemble
end CertificationGaussian
