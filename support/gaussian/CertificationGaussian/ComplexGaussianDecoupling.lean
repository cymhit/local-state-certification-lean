import CertificationGaussian.ComplexGaussianRotation

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I R C : Type*} [Fintype I] [Fintype R] [Fintype C]
  [DecidableEq I] [DecidableEq R] [DecidableEq C]

local instance complexDecoupling_pairedGaussian_probability : IsProbabilityMeasure (pairedGaussian I) := by
  unfold pairedGaussian
  infer_instance

omit [Fintype R] [Fintype C] [DecidableEq I] [DecidableEq R] [DecidableEq C] in
theorem pairedGaussian_complex_pair_integrable (a b : Fin 2 × I) :
    Integrable (fun x : (Fin 2 × I) → ℝ => (x a:ℂ)*(x b:ℂ)) (pairedGaussian I) := by
  classical
  have h : Integrable (fun x : (Fin 2 × I) → ℝ => (↑(x a*x b):ℂ))
      (realGaussianProduct (Fin 2 × I)) := (realGaussianProduct_pair_integrable a b).ofReal
  change Integrable (fun x : (Fin 2 × I) → ℝ => (x a:ℂ)*(x b:ℂ)) (realGaussianProduct (Fin 2 × I))
  simpa only [Complex.ofReal_mul] using h

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
theorem pairedGaussian_complex_pair_integral (a b : Fin 2 × I) :
    (∫ x, (x a:ℂ)*(x b:ℂ) ∂pairedGaussian I) = if a=b then 1 else 0 := by
  change (∫ x : (Fin 2 × I) → ℝ, (x a:ℂ)*(x b:ℂ) ∂realGaussianProduct (Fin 2 × I)) = _
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, realGaussianProduct_second_moment]
  split_ifs <;> rfl

omit [Fintype R] [Fintype C] [DecidableEq I] [DecidableEq R] [DecidableEq C] in
theorem complexCoordinate_mul_star_integrable (i j : I) :
    Integrable (fun x => complexCoordinate x i * star (complexCoordinate x j)) (pairedGaussian I) := by
  simp only [complexCoordinate_mul_star]
  exact ((((pairedGaussian_complex_pair_integrable (0,i) (0,j)).add
    (pairedGaussian_complex_pair_integrable (1,i) (1,j))).add
    ((pairedGaussian_complex_pair_integrable (1,i) (0,j)).const_mul Complex.I)).sub
    ((pairedGaussian_complex_pair_integrable (0,i) (1,j)).const_mul Complex.I)).const_mul (1/2:ℂ)

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
/-- The actual CN(0,I) second moment, including the 1/sqrt(2) normalization. -/
theorem complexCoordinate_mul_star_integral (i j : I) :
    (∫ x, complexCoordinate x i * star (complexCoordinate x j) ∂pairedGaussian I) =
      if i=j then 1 else 0 := by
  have h00 := pairedGaussian_complex_pair_integrable (0,i) (0,j)
  have h11 := pairedGaussian_complex_pair_integrable (1,i) (1,j)
  have h10 := (pairedGaussian_complex_pair_integrable (1,i) (0,j)).const_mul Complex.I
  have h01 := (pairedGaussian_complex_pair_integrable (0,i) (1,j)).const_mul Complex.I
  simp only [complexCoordinate_mul_star]
  rw [integral_const_mul]
  have hs1 := integral_sub ((h00.add h11).add h10) h01
  have hs2 := integral_add (h00.add h11) h10
  have hs3 := integral_add h00 h11
  simp only [Pi.add_apply] at hs1 hs2 hs3
  rw [hs1, hs2, hs3, integral_const_mul, integral_const_mul]
  simp only [pairedGaussian_complex_pair_integral, Prod.mk.injEq, Fin.zero_ne_one,
    show (1:Fin 2) ≠ 0 by decide, false_and, ite_false, true_and, mul_zero, sub_zero]
  by_cases h : i=j <;> norm_num [h]

/-- A sesquilinear matrix polynomial with arbitrary complex rectangular coefficients. -/
def matrixSesquilinear (A : I → I → Matrix R C ℂ) (z w : I → ℂ) : Matrix R C ℂ :=
  ∑ i, ∑ j, (z i * star (w j)) • A i j

/-- Work in the genuine Euclidean continuous-operator space throughout centering. -/
def complexGaussianQuadratic (A : I → I → Matrix R C ℂ) (x : (Fin 2 × I) → ℝ) :
    EuclideanSpace ℂ C →L[ℂ] EuclideanSpace ℂ R :=
  rectangularEuclideanCLM (matrixSesquilinear A (complexCoordinate x) (complexCoordinate x))

omit [DecidableEq I] [DecidableEq R] in
theorem complexGaussianQuadratic_eq_sum (A : I → I → Matrix R C ℂ) (x : (Fin 2 × I) → ℝ) :
    complexGaussianQuadratic A x = ∑ i, ∑ j,
      (complexCoordinate x i * star (complexCoordinate x j)) • rectangularEuclideanCLM (A i j) := by
  simp only [complexGaussianQuadratic, rectangularEuclideanCLM, matrixSesquilinear, map_sum, map_smul]

omit [DecidableEq I] [DecidableEq R] in
theorem complexGaussianQuadratic_term_integrable (A : I → I → Matrix R C ℂ) (i j : I) :
    Integrable (fun x => (complexCoordinate x i * star (complexCoordinate x j)) •
      rectangularEuclideanCLM (A i j)) (pairedGaussian I) :=
  (complexCoordinate_mul_star_integrable i j).smul_const (rectangularEuclideanCLM (A i j))

omit [DecidableEq I] [DecidableEq R] in
theorem complexGaussianQuadratic_integrable (A : I → I → Matrix R C ℂ) :
    Integrable (complexGaussianQuadratic A) (pairedGaussian I) := by
  have hr (i : I) : Integrable (fun x => ∑ j,
      (complexCoordinate x i * star (complexCoordinate x j)) • rectangularEuclideanCLM (A i j))
      (pairedGaussian I) := integrable_finsetSum (μ := pairedGaussian I)
        (f := fun (j : I) (x : (Fin 2 × I) → ℝ) =>
          (complexCoordinate x i * star (complexCoordinate x j)) • rectangularEuclideanCLM (A i j))
        Finset.univ (fun j _ => complexGaussianQuadratic_term_integrable A i j)
  have ht : Integrable (fun x => ∑ i, ∑ j,
      (complexCoordinate x i * star (complexCoordinate x j)) • rectangularEuclideanCLM (A i j))
      (pairedGaussian I) := integrable_finsetSum (μ := pairedGaussian I)
        (f := fun (i : I) (x : (Fin 2 × I) → ℝ) => ∑ j,
          (complexCoordinate x i * star (complexCoordinate x j)) • rectangularEuclideanCLM (A i j))
        Finset.univ (fun i _ => hr i)
  convert ht using 1
  funext x
  exact complexGaussianQuadratic_eq_sum A x

omit [DecidableEq R] in
theorem complexGaussianQuadratic_term_integral (A : I → I → Matrix R C ℂ) (i j : I) :
    (∫ x, (complexCoordinate x i * star (complexCoordinate x j)) •
      rectangularEuclideanCLM (A i j) ∂pairedGaussian I) =
      if i=j then rectangularEuclideanCLM (A i j) else 0 := by
  calc
    _ = (∫ x, complexCoordinate x i * star (complexCoordinate x j) ∂pairedGaussian I) •
        rectangularEuclideanCLM (A i j) := integral_smul_const _ _
    _ = (if i=j then (1:ℂ) else 0) • rectangularEuclideanCLM (A i j) :=
      congrArg (fun c : ℂ => c • rectangularEuclideanCLM (A i j))
        (complexCoordinate_mul_star_integral i j)
    _ = _ := by
      split_ifs
      · exact one_smul ℂ (rectangularEuclideanCLM (A i j))
      · exact zero_smul ℂ (rectangularEuclideanCLM (A i j))

omit [DecidableEq R] in
/-- The actual matrix mean is the sum of diagonal coefficient matrices, with no Hermitian assumption. -/
theorem complexGaussianQuadratic_integral (A : I → I → Matrix R C ℂ) :
    (∫ x, complexGaussianQuadratic A x ∂pairedGaussian I) =
      rectangularEuclideanCLM (∑ i, A i i) := by
  have hr : rectangularEuclideanCLM (∑ i, A i i) = ∑ i, rectangularEuclideanCLM (A i i) := by
    simp only [rectangularEuclideanCLM, map_sum]
  rw [hr]
  simp only [complexGaussianQuadratic_eq_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp only [complexGaussianQuadratic_term_integral]
      simp
    · intro j _
      exact complexGaussianQuadratic_term_integrable A i j
  · intro i _
    exact integrable_finsetSum _ (fun j _ => complexGaussianQuadratic_term_integrable A i j)

/-- Symmetrization follows from the norm of the actual Bochner integral on a probability space. -/
theorem integral_norm_center_le_pair_difference {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → E) (hf : Integrable f μ) :
    (∫ x, ‖f x - ∫ y, f y ∂μ‖ ∂μ) ≤
      ∫ z : Ω × Ω, ‖f z.1-f z.2‖ ∂μ.prod μ := by
  have hp : Integrable (fun z : Ω × Ω => f z.1-f z.2) (μ.prod μ) :=
    (hf.comp_fst μ).sub (hf.comp_snd μ)
  rw [integral_prod _ hp.norm]
  apply integral_mono ((hf.sub (integrable_const _)).norm) hp.norm.integral_prod_left
  intro x
  have he : (∫ y, f x-f y ∂μ) = f x-∫ y, f y ∂μ := by
    rw [integral_sub (integrable_const _) hf]
    simp
  change ‖f x - ∫ y, f y ∂μ‖ ≤ ∫ y, ‖f x-f y‖ ∂μ
  rw [← he]
  exact norm_integral_le_integral_norm _

/-- The scalar polarization identity uses the actual positive sqrt(2), not a distribution assumption. -/
theorem complex_gaussian_rotation_scalar (a b c d : ℂ) :
    a*star b-c*star d =
      ((a+c)/(Real.sqrt 2:ℂ))*star ((b-d)/(Real.sqrt 2:ℂ)) +
      ((a-c)/(Real.sqrt 2:ℂ))*star ((b+d)/(Real.sqrt 2:ℂ)) := by
  have hs : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
  simp only [star_div₀, star_add, star_sub, Complex.star_def, Complex.conj_ofReal]
  field_simp [hs0]
  rw [hs]
  ring

omit [Fintype R] [Fintype C] [DecidableEq I] [DecidableEq R] [DecidableEq C] in
/-- Arbitrary rectangular coefficients suffice: the rotated difference is the sum of the two orders. -/
theorem matrixSesquilinear_rotation_difference (A : I → I → Matrix R C ℂ)
    (z w : I → ℂ) :
    matrixSesquilinear A z z - matrixSesquilinear A w w =
      matrixSesquilinear A (complexPairRotation I (z,w)).1 (complexPairRotation I (z,w)).2 +
      matrixSesquilinear A (complexPairRotation I (z,w)).2 (complexPairRotation I (z,w)).1 := by
  simp only [matrixSesquilinear, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← sub_smul, ← add_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact complex_gaussian_rotation_scalar (z i) (z j) (w i) (w j)

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
/-- Integral transport through the actual complex Gaussian rotation law. -/
theorem complexPairRotation_integral (f : ((I → ℂ) × (I → ℂ)) → ℝ) (hf : Continuous f) :
    (∫ z, f (complexPairRotation I (complexPairCoordinates I z))
      ∂(pairedGaussian I).prod (pairedGaussian I)) =
      ∫ z, f (complexPairCoordinates I z) ∂(pairedGaussian I).prod (pairedGaussian I) := by
  have hm : Measurable (fun z => complexPairRotation I (complexPairCoordinates I z)) := by fun_prop
  rw [← integral_map_of_stronglyMeasurable hm hf.stronglyMeasurable,
    complexPairRotation_map I,
    integral_map_of_stronglyMeasurable (complexPairCoordinates_continuous I).measurable hf.stronglyMeasurable]

omit [DecidableEq I] [DecidableEq R] in
@[fun_prop] theorem matrixSesquilinear_operator_continuous (A : I → I → Matrix R C ℂ) :
    Continuous (fun z : (I → ℂ) × (I → ℂ) => rectangularEuclideanCLM (matrixSesquilinear A z.1 z.2)) := by
  simp only [rectangularEuclideanCLM, matrixSesquilinear, map_sum, map_smul]
  fun_prop

omit [Fintype I] [DecidableEq I] [DecidableEq R] in
theorem rectangularEuclideanCLM_add (A B : Matrix R C ℂ) :
    rectangularEuclideanCLM (A+B) = rectangularEuclideanCLM A + rectangularEuclideanCLM B := by
  simp only [rectangularEuclideanCLM, map_add]

omit [Fintype I] [DecidableEq I] [DecidableEq R] in
theorem rectangularEuclideanCLM_sub (A B : Matrix R C ℂ) :
    rectangularEuclideanCLM (A-B) = rectangularEuclideanCLM A - rectangularEuclideanCLM B := by
  simp only [rectangularEuclideanCLM, map_sub]

omit [DecidableEq R] in
/-- The actual difference expectation becomes the two-order bilinear sum by Gaussian rotation. -/
theorem complexGaussianQuadratic_difference_integral (A : I → I → Matrix R C ℂ) :
    (∫ z, ‖complexGaussianQuadratic A z.1-complexGaussianQuadratic A z.2‖
      ∂(pairedGaussian I).prod (pairedGaussian I)) =
      ∫ z, ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2) +
        rectangularEuclideanCLM (complexGaussianBilinear A z.2 z.1)‖
        ∂(pairedGaussian I).prod (pairedGaussian I) := by
  let f : ((I → ℂ) × (I → ℂ)) → ℝ := fun z =>
    ‖rectangularEuclideanCLM (matrixSesquilinear A z.1 z.2) +
      rectangularEuclideanCLM (matrixSesquilinear A z.2 z.1)‖
  have hf : Continuous f := by
    dsimp [f]
    have h := matrixSesquilinear_operator_continuous A
    exact (h.add (h.comp continuous_swap)).norm
  have he (z : ((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ)) :
      ‖complexGaussianQuadratic A z.1-complexGaussianQuadratic A z.2‖ =
        f (complexPairRotation I (complexPairCoordinates I z)) := by
    simp only [complexGaussianQuadratic, ← rectangularEuclideanCLM_sub,
      matrixSesquilinear_rotation_difference, rectangularEuclideanCLM_add]
    rfl
  simp_rw [he]
  exact complexPairRotation_integral f hf

omit [DecidableEq I] [DecidableEq R] in
theorem complexGaussianBilinear_operator_integrable (A : I → I → Matrix R C ℂ) :
    Integrable (fun z => rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2))
      ((pairedGaussian I).prod (pairedGaussian I)) := by
  have hm : Continuous (fun z : ((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ) =>
      rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)) := by
    simp only [rectangularEuclideanCLM, complexGaussianBilinear, map_sum, map_smul]
    unfold complexCoordinate
    fun_prop
  exact (integrable_norm_iff hm.aestronglyMeasurable).mp (complexGaussianBilinear_opNorm_integrable A)

omit [DecidableEq I] [DecidableEq R] in
/-- Swapping two independent copies gives the same second summand expectation. -/
theorem complexGaussianBilinear_two_order_bound (A : I → I → Matrix R C ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2) +
        rectangularEuclideanCLM (complexGaussianBilinear A z.2 z.1)‖
        ∂(pairedGaussian I).prod (pairedGaussian I)) ≤
      2 * ∫ z, ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)‖
        ∂(pairedGaussian I).prod (pairedGaussian I) := by
  have hy := complexGaussianBilinear_operator_integrable A
  have hs := hy.swap
  have h := integral_mono (hy.add hs).norm (hy.norm.add hs.norm)
    (fun z => norm_add_le _ _)
  have hadd := integral_add hy.norm hs.norm
  simp only [Pi.add_apply] at h hadd
  rw [hadd] at h
  have hswap : (∫ z, ‖rectangularEuclideanCLM (complexGaussianBilinear A z.2 z.1)‖
      ∂(pairedGaussian I).prod (pairedGaussian I)) =
      ∫ z, ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)‖
        ∂(pairedGaussian I).prod (pairedGaussian I) :=
      integral_prod_swap (μ := pairedGaussian I) (ν := pairedGaussian I)
        (fun z : ((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ) =>
          ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)‖)
  dsimp only [Function.comp_def, Prod.swap] at h
  rw [hswap] at h
  linarith

omit [DecidableEq R] in
/-- Actual centered complex Gaussian quadratic chaos is bounded by two decoupled copies.
No symmetry or Hermitian condition on the rectangular coefficient tensor is needed. -/
theorem complexGaussianQuadratic_decoupling (A : I → I → Matrix R C ℂ) :
    (∫ x, ‖complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i)‖ ∂pairedGaussian I) ≤
      2 * ∫ z, ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)‖
        ∂(pairedGaussian I).prod (pairedGaussian I) := by
  have h := integral_norm_center_le_pair_difference (pairedGaussian I) (complexGaussianQuadratic A)
    (complexGaussianQuadratic_integrable A)
  rw [complexGaussianQuadratic_integral, complexGaussianQuadratic_difference_integral] at h
  exact h.trans (complexGaussianBilinear_two_order_bound A)

/-- The centered four-flattening theorem for the actual standard complex Gaussian measure. -/
theorem complexGaussianQuadratic_expectation_bound (A : I → I → Matrix R C ℂ) :
    (∫ x, ‖complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i)‖ ∂pairedGaussian I) ≤
      (4*gaussianMatrixChaosConstant) * Real.sqrt
        (Real.log (2*((Fintype.card R:ℝ)+Fintype.card C)) *
          Real.log (2*(Fintype.card I:ℝ)*((Fintype.card R:ℝ)+Fintype.card C))) *
        gaussianChaosFlatteningNorm A := by
  have h := (complexGaussianQuadratic_decoupling A).trans
    (mul_le_mul_of_nonneg_left (complexGaussianBilinear_expectation_bound A) (by norm_num : (0:ℝ)≤2))
  convert h using 1
  ring

/-- The two logarithms reduce to a single log in the equal-dimension application. -/
theorem gaussian_equal_dimension_log_factor (d : ℝ) (hd : 1 ≤ d) :
    Real.sqrt (Real.log (4*d) * Real.log (4*d^2)) ≤ 2*Real.log (2*d) := by
  have hd0 : 0 < d := by linarith
  have hL : 0 ≤ Real.log (2*d) := Real.log_nonneg (by linarith)
  have h4 : 0 ≤ Real.log (4*d) := Real.log_nonneg (by linarith)
  have hfirst : Real.log (4*d) ≤ 2*Real.log (2*d) := by
    rw [show 4*d=2*(2*d) by ring, Real.log_mul (by norm_num) (by positivity)]
    have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ)≤2*d)
    linarith
  have hsecond : Real.log (4*d^2) = 2*Real.log (2*d) := by
    rw [show 4*d^2=(2*d)^2 by ring, Real.log_pow]
    norm_num
  rw [hsecond]
  have hp : 0 ≤ Real.log (4*d)*(2*Real.log (2*d)) := mul_nonneg h4 (by positivity)
  have hs := Real.sq_sqrt hp
  have hbound := mul_le_mul_of_nonneg_right hfirst (by positivity : 0 ≤ 2*Real.log (2*d))
  nlinarith [Real.sqrt_nonneg (Real.log (4*d)*(2*Real.log (2*d)))]

/-- Equal Gaussian and matrix dimensions, ready for Weyl coefficients; empty dimension is also valid. -/
theorem complexGaussianQuadratic_equal_dimension_bound (A : I → I → Matrix I I ℂ) :
    (∫ x, ‖complexGaussianQuadratic A x-rectangularEuclideanCLM (∑ i, A i i)‖ ∂pairedGaussian I) ≤
      (8*gaussianMatrixChaosConstant) * Real.log (2*(Fintype.card I:ℝ)) * gaussianChaosFlatteningNorm A := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
    have hq (x : (Fin 2 × I) → ℝ) : complexGaussianQuadratic A x = 0 := Subsingleton.elim _ _
    simp [hq]
  | inr hI =>
    have hd : (1:ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hl := gaussian_equal_dimension_log_factor (Fintype.card I) hd
    have h := complexGaussianQuadratic_expectation_bound A
    rw [show 2*((Fintype.card I:ℝ)+Fintype.card I)=4*(Fintype.card I:ℝ) by ring,
      show 2*(Fintype.card I:ℝ)*((Fintype.card I:ℝ)+Fintype.card I)=4*(Fintype.card I:ℝ)^2 by ring] at h
    have hb := h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num) gaussianMatrixChaosConstant_pos.le))
      (gaussianChaosFlatteningNorm_nonneg A))
    convert hb using 1
    ring

end CertificationGaussian
