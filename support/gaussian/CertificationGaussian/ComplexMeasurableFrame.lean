import CertificationGaussian.MeasurableGaussianFrameBound

/-! # Complex frames of actual measurable projector ensembles

The complex operator is the genuine Bochner integral. Its restriction agrees
with the real matrix frame on Hermitian inputs, which is the precise subspace
needed for Gaussian and sphere energies.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

section ComplexFrame
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

def integralComplexHilbertFrame (V : Ω → E) : E →L[ℂ] E :=
  ∫ s, InnerProductSpace.rankOne ℂ (V s) (V s) ∂ν

omit [CompleteSpace E] in
theorem integralComplexHilbertFrame_integrable (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) :
    Integrable (fun s => InnerProductSpace.rankOne ℂ (V s) (V s)) ν := by
  have hc : Continuous (fun x : E => InnerProductSpace.rankOne ℂ x x) := by
    change Continuous (fun x : E => (ContinuousLinearMap.smulRightL ℂ E E) (innerSL ℂ x) x)
    exact ((ContinuousLinearMap.smulRightL ℂ E E).continuous.comp (innerSL ℂ).continuous).clm_apply continuous_id
  apply (integrable_const (K^2)).mono' (hc.comp_aestronglyMeasurable hV)
  filter_upwards [hbound] with s hs
  rw [InnerProductSpace.norm_rankOne, ← pow_two]
  exact (sq_le_sq₀ (norm_nonneg _) hK).mpr hs

theorem integralComplexHilbertFrame_inner (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (x y : E) :
    inner ℂ y (integralComplexHilbertFrame ν V x) =
      ∫ s, inner ℂ (V s) x * inner ℂ y (V s) ∂ν := by
  have hF := integralComplexHilbertFrame_integrable ν V hV hK hbound
  have hFx : Integrable (fun s => InnerProductSpace.rankOne ℂ (V s) (V s) x) ν := by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℂ E x).integrable_comp hF
  rw [integralComplexHilbertFrame, ContinuousLinearMap.integral_apply hF x,
    ← integral_inner (𝕜 := ℂ) hFx]
  simp only [InnerProductSpace.rankOne_apply, inner_smul_right]

omit [CompleteSpace E] in
theorem integralComplexHilbertFrame_pair_integrable (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (x y : E) :
    Integrable (fun s => inner ℂ (V s) x * inner ℂ y (V s)) ν := by
  have h := Integrable.const_inner (𝕜 := ℂ) y
    ((ContinuousLinearMap.apply ℂ E x).integrable_comp
      (integralComplexHilbertFrame_integrable ν V hV hK hbound))
  simpa only [ContinuousLinearMap.apply_apply, InnerProductSpace.rankOne_apply,
    inner_smul_right] using h

omit [CompleteSpace E] in
theorem integralComplexHilbertFrame_square_integrable (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (x : E) :
    Integrable (fun s => ‖inner ℂ (V s) x‖^2) ν := by
  have hi := (integralComplexHilbertFrame_pair_integrable ν V hV hK hbound x x).re
  convert hi using 1
  funext s
  change ‖inner ℂ (V s) x‖^2 = (inner ℂ (V s) x * inner ℂ x (V s)).re
  rw [← inner_conj_symm x (V s), Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem integralComplexHilbertFrame_norm_le (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K c : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (hc : 0 ≤ c)
    (hquad : ∀ x, (∫ s, ‖inner ℂ (V s) x‖^2 ∂ν) ≤ c * ‖x‖^2) :
    ‖integralComplexHilbertFrame ν V‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hc
  intro x y hx hy
  have hp := integralComplexHilbertFrame_pair_integrable ν V hV hK hbound x y
  have hi (z : E) := integralComplexHilbertFrame_square_integrable ν V hV hK hbound z
  have hxy : ∀ s, (inner ℂ (V s) x * inner ℂ y (V s)).re ≤
      (‖inner ℂ (V s) x‖^2 + ‖inner ℂ (V s) y‖^2)/2 := by
    intro s
    have h := (Complex.re_le_norm (inner ℂ (V s) x * inner ℂ y (V s)))
    rw [norm_mul, norm_inner_symm y] at h
    nlinarith [sq_nonneg (‖inner ℂ (V s) x‖-‖inner ℂ (V s) y‖)]
  have hle := integral_mono hp.re (((hi x).add (hi y)).div_const 2) hxy
  rw [integral_div] at hle
  simp only [Pi.add_apply] at hle
  rw [integral_add (hi x) (hi y)] at hle
  change (∫ s, (inner ℂ (V s) x * inner ℂ y (V s)).re ∂ν) ≤
    ((∫ s, ‖inner ℂ (V s) x‖^2 ∂ν) + (∫ s, ‖inner ℂ (V s) y‖^2 ∂ν))/2 at hle
  have hqx := hquad x
  have hqy := hquad y
  rw [hx, one_pow, mul_one] at hqx
  rw [hy, one_pow, mul_one] at hqy
  have hEq : (inner ℂ (integralComplexHilbertFrame ν V x) y).re =
      ∫ s, (inner ℂ (V s) x * inner ℂ y (V s)).re ∂ν := by
    rw [← inner_conj_symm (integralComplexHilbertFrame ν V x) y, Complex.conj_re,
      integralComplexHilbertFrame_inner ν V hV hK hbound]
    exact (integral_re hp).symm
  change (inner ℂ (integralComplexHilbertFrame ν V x) y).re ≤ c
  rw [hEq]
  linarith

theorem integralComplexHilbertFrame_adjoint (V : Ω → E)
    (hV : AEStronglyMeasurable V ν) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) :
    ContinuousLinearMap.adjoint (integralComplexHilbertFrame ν V) = integralComplexHilbertFrame ν V := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm (integralComplexHilbertFrame ν V y) x,
    integralComplexHilbertFrame_inner ν V hV hK hbound,
    integralComplexHilbertFrame_inner ν V hV hK hbound, ← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by simp only [map_mul, inner_conj_symm]; ring

theorem integralComplexHilbertFrame_map (V : Ω → E) (hV : AEStronglyMeasurable V ν)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (R : E →L[ℂ] E) :
    integralComplexHilbertFrame ν (fun s => R (V s)) =
      R.comp ((integralComplexHilbertFrame ν V).comp (ContinuousLinearMap.adjoint R)) := by
  have hRV := R.continuous.comp_aestronglyMeasurable hV
  have hRb : ∀ᵐ s ∂ν, ‖R (V s)‖ ≤ ‖R‖ * K := by
    filter_upwards [hbound] with s hs
    exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [integralComplexHilbertFrame_inner ν _ hRV (mul_nonneg (norm_nonneg _) hK) hRb]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left,
    integralComplexHilbertFrame_inner ν V hV hK hbound]
  simp only [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]

end ComplexFrame

section MatrixFrame
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (ν : Measure Ω) [IsProbabilityMeasure ν]

def integralComplexMatrixFrame (B : Ω → Matrix I I ℂ) :
    EuclideanSpace ℂ (I × I) →L[ℂ] EuclideanSpace ℂ (I × I) :=
  integralComplexHilbertFrame ν (fun s => matrixHilbertSchmidt (B s))

omit [DecidableEq I] in
theorem matrixHilbertSchmidt_complex_inner (A B : Matrix I I ℂ) :
    inner ℂ (matrixHilbertSchmidt A) (matrixHilbertSchmidt B) =
      (A.conjTranspose * B).trace := by
  simp only [matrixHilbertSchmidt, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fintype.sum_prod_type, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

private def complexFrameRealTracePairing (A : Matrix I I ℂ) : Matrix I I ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (A * M).trace.re
      map_add' := by intro M N; simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by intro c M; simp [Matrix.trace_smul] }

theorem vectorRankOne_trace_norm_sq_le (A : Matrix I I ℂ) (u : EuclideanSpace ℂ I)
    (hu : ‖u‖ = 1) :
    ‖(A * vectorRankOne u u).trace‖^2 ≤
      (A.conjTranspose * A * vectorRankOne u u).trace.re := by
  rw [vectorRankOne_star_square_trace, vectorRankOne_trace_pairing, sphereQuadraticForm_eq_inner]
  have h := norm_inner_le_norm (𝕜 := ℂ) u (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A u)
  rw [hu, one_mul] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h

/-- The actual first moment controls the complex frame on all complex matrices. -/
theorem measurableRankOneComplexFrame_norm_le (u : Ω → EuclideanSpace ℂ I)
    (hu : AEStronglyMeasurable u ν) (hunit : ∀ᵐ s ∂ν, ‖u s‖ = 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hmean : (∫ s, vectorRankOne (u s) (u s) ∂ν) =
      (c : ℂ) • (1 : Matrix I I ℂ)) :
    ‖integralComplexMatrixFrame ν (fun s => vectorRankOne (u s) (u s))‖ ≤ c := by
  let V := fun s => matrixHilbertSchmidt (vectorRankOne (u s) (u s))
  have hcont : Continuous (fun v : EuclideanSpace ℂ I => matrixHilbertSchmidt (vectorRankOne v v)) := by
    unfold matrixHilbertSchmidt vectorRankOne
    fun_prop
  have hV : AEStronglyMeasurable V ν := hcont.comp_aestronglyMeasurable hu
  have hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ 1 := by
    filter_upwards [hunit] with s hs
    have hn : ‖V s‖^2 = 1 := by
      dsimp only [V]
      rw [matrixHilbertSchmidt_norm_sq _ (vectorRankOne_self_hermitian _),
        vectorRankOne_self_sq _ hs, vectorRankOne_self_trace _ hs, Complex.one_re]
    nlinarith [norm_nonneg (V s)]
  apply integralComplexHilbertFrame_norm_le ν V hV (by norm_num : (0 : ℝ) ≤ 1) hbound hc
  intro x
  let A : Matrix I I ℂ := fun i j => x (i,j)
  have hx : matrixHilbertSchmidt A = x := rfl
  have hP := measurableRankOne_integrable ν u hu hunit
  have hR : Integrable (fun s => (A.conjTranspose * A * vectorRankOne (u s) (u s)).trace.re) ν :=
    (complexFrameRealTracePairing (A.conjTranspose * A)).integrable_comp hP
  have hL := integralComplexHilbertFrame_square_integrable ν V hV
    (by norm_num : (0 : ℝ) ≤ 1) hbound x
  calc
    _ ≤ ∫ s, (A.conjTranspose * A * vectorRankOne (u s) (u s)).trace.re ∂ν := by
      apply integral_mono_ae hL hR
      filter_upwards [hunit] with s hs
      dsimp only [V]
      rw [← hx, matrixHilbertSchmidt_complex_inner,
        (vectorRankOne_self_hermitian (u s)).eq,
        Matrix.trace_mul_comm (vectorRankOne (u s) (u s)) A]
      exact vectorRankOne_trace_norm_sq_le A (u s) hs
    _ = c * ‖x‖^2 := by
      have hm := (complexFrameRealTracePairing (A.conjTranspose * A)).integral_comp_comm (μ := ν) hP
      change (∫ s, (A.conjTranspose * A * vectorRankOne (u s) (u s)).trace.re ∂ν) =
        (A.conjTranspose * A * (∫ s, vectorRankOne (u s) (u s) ∂ν)).trace.re at hm
      rw [hmean] at hm
      simpa only [Matrix.mul_smul, mul_one, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        matrixHilbertSchmidt_star_square, hx] using hm

omit [DecidableEq I] in
private theorem hermitian_trace_product_real (A B : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : ((A*B).trace.re : ℂ) = (A*B).trace := by
  apply Complex.ext
  · simp
  · have h : star (A*B).trace = (A*B).trace := by
      simp only [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq]
      exact Matrix.trace_mul_comm B A
    have hh := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hh
    simp only [Complex.ofReal_im]
    linarith

omit [DecidableEq I] in
/-- The equality is asserted only for Hermitian inputs. -/
theorem integralComplexMatrixFrame_eq_real_on_hermitian
    (B : Ω → Matrix I I ℂ) (hB : AEStronglyMeasurable B ν)
    (hH : ∀ᵐ s ∂ν, (B s).IsHermitian) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    integralComplexMatrixFrame ν B (matrixHilbertSchmidt A) =
      integralMatrixFrame ν B (matrixHilbertSchmidt A) := by
  have hc : Continuous (matrixHilbertSchmidt : Matrix I I ℂ → EuclideanSpace ℂ (I × I)) := by
    unfold matrixHilbertSchmidt
    fun_prop
  have hV := hc.comp_aestronglyMeasurable hB
  rw [integralComplexMatrixFrame, integralComplexHilbertFrame,
    ContinuousLinearMap.integral_apply (integralComplexHilbertFrame_integrable ν _ hV hK hbound),
    integralMatrixFrame, integralHilbertFrame,
    ContinuousLinearMap.integral_apply (integralHilbertFrame_integrable ν _ hV hK hbound)]
  apply integral_congr_ae
  filter_upwards [hH] with s hs
  simp only [InnerProductSpace.rankOne_apply, matrixHilbertSchmidt_complex_inner,
    hs.eq, matrixHilbertSchmidt_inner _ _ hs]
  rw [← hermitian_trace_product_real _ _ hs hA]
  rfl

end MatrixFrame
end CertificationGaussian
