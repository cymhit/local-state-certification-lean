import CertificationGaussian.GaussianChaosFlattenings
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I R C : Type*} [Fintype I] [Fintype R] [Fintype C]
  [DecidableEq I] [DecidableEq R] [DecidableEq C]

/-- The genuine bilinear series in two independent standard-real Gaussian coordinate families. -/
def gaussianMatrixChaos (A : I → I → Matrix R C ℂ) (x y : I → ℝ) : Matrix R C ℂ :=
  ∑ i, ∑ j, ((x i : ℂ)*(y j : ℂ)) • A i j

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype R] [Fintype C] in
theorem gaussianMatrixChaos_conditional (A : I → I → Matrix R C ℂ) (x y : I → ℝ) :
    gaussianMatrixChaos A x y =
      gaussianMatrixSeries (fun j => gaussianMatrixSeries (fun i => A i j) x) y := by
  simp only [gaussianMatrixChaos, gaussianMatrixSeries, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

omit [DecidableEq I] [DecidableEq R] in
/-- A finite product envelope is used only to justify Fubini, not in the final norm bound. -/
theorem gaussianMatrixChaos_opNorm_le (A : I → I → Matrix R C ℂ) (x y : I → ℝ) :
    ‖rectangularEuclideanCLM (gaussianMatrixChaos A x y)‖ ≤
      ∑ i, ∑ j, |x i| * |y j| * ‖rectangularEuclideanCLM (A i j)‖ := by
  simp only [rectangularEuclideanCLM_norm, gaussianMatrixChaos]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ =>
    (norm_sum_le _ _).trans (by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, le_refl])))

omit [DecidableEq I] [DecidableEq R] in
theorem gaussianMatrixChaos_opNorm_continuous (A : I → I → Matrix R C ℂ) :
    Continuous (fun z : (I → ℝ) × (I → ℝ) => ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖) := by
  simp only [rectangularEuclideanCLM, gaussianMatrixChaos, map_sum, map_smul]
  fun_prop

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] [DecidableEq I] in
theorem realGaussianProduct_abs_coordinate_integrable (i : I) :
    Integrable (fun x : I → ℝ => |x i|) (realGaussianProduct I) := by
  have h := (realGaussianProduct_polynomial_integrable (MvPolynomial.X i)).norm
  simpa only [MvPolynomial.eval_X, Real.norm_eq_abs] using h

omit [DecidableEq I] [DecidableEq R] in
theorem gaussianMatrixChaos_opNorm_integrable (A : I → I → Matrix R C ℂ) :
    Integrable (fun z : (I → ℝ) × (I → ℝ) => ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖)
      ((realGaussianProduct I).prod (realGaussianProduct I)) := by
  have he : Integrable (fun z : (I → ℝ) × (I → ℝ) =>
      ∑ i, ∑ j, |z.1 i| * |z.2 j| * ‖rectangularEuclideanCLM (A i j)‖)
      ((realGaussianProduct I).prod (realGaussianProduct I)) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact ((realGaussianProduct_abs_coordinate_integrable i).mul_prod
      (realGaussianProduct_abs_coordinate_integrable j)).mul_const _
  apply he.mono' (gaussianMatrixChaos_opNorm_continuous A).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_norm] using gaussianMatrixChaos_opNorm_le A z.1 z.2

omit [DecidableEq I] [DecidableEq R] in
/-- Actual product-measure expectation equals the iterated conditional expectation. -/
theorem gaussianMatrixChaos_integral_prod (A : I → I → Matrix R C ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
      ∂(realGaussianProduct I).prod (realGaussianProduct I)) =
      ∫ x, ∫ y, ‖rectangularEuclideanCLM
        (gaussianMatrixSeries (fun j => gaussianMatrixSeries (fun i => A i j) x) y)‖
        ∂realGaussianProduct I ∂realGaussianProduct I := by
  rw [integral_prod _ (gaussianMatrixChaos_opNorm_integrable A)]
  simp only [gaussianMatrixChaos_conditional]

/-- Integrating the whole conditional block bound loses only an absolute factor of two later. -/
theorem gaussianMatrixChaos_expectation_le_blocks (A : I → I → Matrix R C ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
      ∂(realGaussianProduct I).prod (realGaussianProduct I)) ≤
      gaussianMatrixExpectationConstant * Real.sqrt (Real.log (2*((Fintype.card R:ℝ)+Fintype.card C))) *
      ((∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries (chaosRowCoefficient A) x)‖
          ∂realGaussianProduct I) +
        ∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries (chaosColumnCoefficient A) x)‖
          ∂realGaussianProduct I) := by
  have hr := (rectangularGaussian_opNorm_memLp (chaosRowCoefficient A) 1 (by simp)).integrable le_rfl
  have hc := (rectangularGaussian_opNorm_memLp (chaosColumnCoefficient A) 1 (by simp)).integrable le_rfl
  have hi := (gaussianMatrixChaos_opNorm_integrable A).integral_prod_left
  rw [integral_prod _ (gaussianMatrixChaos_opNorm_integrable A)]
  rw [← integral_add hr hc, ← integral_const_mul]
  apply integral_mono hi ((hr.add hc).const_mul _)
  intro x
  simp only [gaussianMatrixChaos_conditional]
  have h := rectangularGaussian_expectation_bound_blocks
    (fun j => gaussianMatrixSeries (fun i => A i j) x)
  rw [← gaussianMatrixSeries_blockRow, ← gaussianMatrixSeries_blockColumn] at h
  exact h.trans (mul_le_mul_of_nonneg_left (max_le_add_of_nonneg
    (norm_nonneg _) (norm_nonneg _)) (mul_nonneg gaussianMatrixExpectationConstant_pos.le (Real.sqrt_nonneg _)))

/-- The common maximum of all four genuine Euclidean flattening norms. -/
def gaussianChaosFlatteningNorm (A : I → I → Matrix R C ℂ) : ℝ :=
  max (max ‖rectangularEuclideanCLM (chaosFlattening₁ A)‖ ‖rectangularEuclideanCLM (chaosFlattening₂ A)‖)
    (max ‖rectangularEuclideanCLM (chaosFlattening₃ A)‖ ‖rectangularEuclideanCLM (chaosFlattening₄ A)‖)

omit [DecidableEq R] in
theorem gaussianChaosFlatteningNorm_nonneg (A : I → I → Matrix R C ℂ) :
    0 ≤ gaussianChaosFlatteningNorm A := by
  exact (norm_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))

private theorem block_log_bounds (m r c : ℝ) (hm : 1 ≤ m) (hr : 1 ≤ r) (hc : 1 ≤ c) :
    Real.sqrt (Real.log (2*(r+m*c))) ≤ Real.sqrt (Real.log (2*m*(r+c))) ∧
    Real.sqrt (Real.log (2*(m*r+c))) ≤ Real.sqrt (Real.log (2*m*(r+c))) := by
  have hm0 : 0 ≤ m := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hmr : r ≤ m*r := by nlinarith
  have hmc : c ≤ m*c := by nlinarith
  constructor
  · apply Real.sqrt_le_sqrt
    apply Real.log_le_log (by positivity)
    nlinarith
  · apply Real.sqrt_le_sqrt
    apply Real.log_le_log (by positivity)
    nlinarith

/-- Both second Gaussian estimates are controlled by the same four-flattening norm. -/
theorem gaussianChaos_blocks_expectation_bound [Nonempty I] [Nonempty R] [Nonempty C]
    (A : I → I → Matrix R C ℂ) :
    ((∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries (chaosRowCoefficient A) x)‖
        ∂realGaussianProduct I) +
      ∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries (chaosColumnCoefficient A) x)‖
        ∂realGaussianProduct I) ≤
      2 * gaussianMatrixExpectationConstant *
        Real.sqrt (Real.log (2*(Fintype.card I:ℝ)*((Fintype.card R:ℝ)+Fintype.card C))) *
        gaussianChaosFlatteningNorm A := by
  have hm : (1:ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hr : (1:ℝ) ≤ Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hc : (1:ℝ) ≤ Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hl := block_log_bounds (Fintype.card I) (Fintype.card R) (Fintype.card C) hm hr hc
  have h13 : max ‖rectangularEuclideanCLM (chaosFlattening₁ A)‖
      ‖rectangularEuclideanCLM (chaosFlattening₃ A)‖ ≤ gaussianChaosFlatteningNorm A :=
    max_le ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
  have h42 : max ‖rectangularEuclideanCLM (chaosFlattening₄ A)‖
      ‖rectangularEuclideanCLM (chaosFlattening₂ A)‖ ≤ gaussianChaosFlatteningNorm A :=
    max_le ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_left _ _))
  have hrow := (gaussianChaosRow_expectation_bound A).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hl.1 gaussianMatrixExpectationConstant_pos.le) h13
    (le_trans (norm_nonneg _) (le_max_left _ _))
    (mul_nonneg gaussianMatrixExpectationConstant_pos.le (Real.sqrt_nonneg _)))
  have hcol := (gaussianChaosColumn_expectation_bound A).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hl.2 gaussianMatrixExpectationConstant_pos.le) h42
    (le_trans (norm_nonneg _) (le_max_left _ _))
    (mul_nonneg gaussianMatrixExpectationConstant_pos.le (Real.sqrt_nonneg _)))
  nlinarith [add_le_add hrow hcol]

/-- An absolute constant, independent of all three dimensions and every coefficient matrix. -/
def gaussianMatrixChaosConstant : ℝ := 2 * gaussianMatrixExpectationConstant^2

theorem gaussianMatrixChaosConstant_pos : 0 < gaussianMatrixChaosConstant := by
  unfold gaussianMatrixChaosConstant
  have h := gaussianMatrixExpectationConstant_pos
  positivity

/-- The actual product-Gaussian second-order matrix bound with all four flattenings. -/
theorem gaussianMatrixChaos_expectation_bound_nonempty [Nonempty I] [Nonempty R] [Nonempty C]
    (A : I → I → Matrix R C ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
      ∂(realGaussianProduct I).prod (realGaussianProduct I)) ≤
      gaussianMatrixChaosConstant * Real.sqrt
        (Real.log (2*((Fintype.card R:ℝ)+Fintype.card C)) *
          Real.log (2*(Fintype.card I:ℝ)*((Fintype.card R:ℝ)+Fintype.card C))) *
        gaussianChaosFlatteningNorm A := by
  have hr : (1:ℝ) ≤ Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hc : (1:ℝ) ≤ Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hlog : 0 ≤ Real.log (2*((Fintype.card R:ℝ)+Fintype.card C)) :=
    Real.log_nonneg (by linarith)
  have h := (gaussianMatrixChaos_expectation_le_blocks A).trans
    (mul_le_mul_of_nonneg_left (gaussianChaos_blocks_expectation_bound A)
      (mul_nonneg gaussianMatrixExpectationConstant_pos.le (Real.sqrt_nonneg _)))
  convert h using 1
  rw [Real.sqrt_mul hlog]
  unfold gaussianMatrixChaosConstant
  ring

/-- The same universal bound includes empty Gaussian families and either empty matrix dimension. -/
theorem gaussianMatrixChaos_expectation_bound (A : I → I → Matrix R C ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
      ∂(realGaussianProduct I).prod (realGaussianProduct I)) ≤
      gaussianMatrixChaosConstant * Real.sqrt
        (Real.log (2*((Fintype.card R:ℝ)+Fintype.card C)) *
          Real.log (2*(Fintype.card I:ℝ)*((Fintype.card R:ℝ)+Fintype.card C))) *
        gaussianChaosFlatteningNorm A := by
  have hnonneg : 0 ≤ gaussianMatrixChaosConstant * Real.sqrt
        (Real.log (2*((Fintype.card R:ℝ)+Fintype.card C)) *
          Real.log (2*(Fintype.card I:ℝ)*((Fintype.card R:ℝ)+Fintype.card C))) *
        gaussianChaosFlatteningNorm A := mul_nonneg
      (mul_nonneg gaussianMatrixChaosConstant_pos.le (Real.sqrt_nonneg _))
      (gaussianChaosFlatteningNorm_nonneg A)
  cases isEmpty_or_nonempty I with
  | inl hI =>
    have hz (x y : I → ℝ) : rectangularEuclideanCLM (gaussianMatrixChaos A x y) = 0 := by
      simp [gaussianMatrixChaos, rectangularEuclideanCLM]
    simpa only [hz, norm_zero, integral_zero] using hnonneg
  | inr hI =>
    cases isEmpty_or_nonempty R with
    | inl hR =>
      have hz (x y : I → ℝ) : rectangularEuclideanCLM (gaussianMatrixChaos A x y) = 0 :=
        Subsingleton.elim _ _
      simpa only [hz, norm_zero, integral_zero] using hnonneg
    | inr hR =>
      cases isEmpty_or_nonempty C with
      | inl hC =>
        have hz (x y : I → ℝ) : rectangularEuclideanCLM (gaussianMatrixChaos A x y) = 0 :=
          Subsingleton.elim _ _
        simpa only [hz, norm_zero, integral_zero] using hnonneg
      | inr hC => exact gaussianMatrixChaos_expectation_bound_nonempty A

end CertificationGaussian
