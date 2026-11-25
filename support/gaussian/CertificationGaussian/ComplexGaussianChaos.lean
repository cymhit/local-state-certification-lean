import CertificationGaussian.GaussianChaosExpectation
import CertificationGaussian.GaussianBlocks

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I R C : Type*} [Fintype I] [Fintype R] [Fintype C]
  [DecidableEq I] [DecidableEq R] [DecidableEq C]

local instance complexChaos_pairedGaussian_probability : IsProbabilityMeasure (pairedGaussian I) := by
  unfold pairedGaussian
  infer_instance

/-- Regroup the existing paired coordinates into their two real Gaussian vectors. -/
def realImagCoordinates (I : Type*) : ((Fin 2 × I) → ℝ) ≃ᵐ ((I → ℝ) × (I → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : I ⊕ I => ℝ) (pairSumIndex I)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ I => ℝ))

omit [Fintype R] [Fintype C] [DecidableEq I] [DecidableEq R] [DecidableEq C] in
theorem realImagCoordinates_preserving : MeasurePreserving (realImagCoordinates I)
    (pairedGaussian I) ((realGaussianProduct I).prod (realGaussianProduct I)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ I => gaussianReal 0 1)).comp
    (measurePreserving_piCongrLeft (fun _ : I ⊕ I => gaussianReal 0 1) (pairSumIndex I))

omit [Fintype R] [Fintype C] [DecidableEq I] [DecidableEq R] [DecidableEq C] in
theorem pairedComponent_preserving (s : Fin 2) :
    MeasurePreserving (fun x : (Fin 2 × I) → ℝ => fun i => x (s,i))
      (pairedGaussian I) (realGaussianProduct I) := by
  fin_cases s
  · exact measurePreserving_fst.comp realImagCoordinates_preserving
  · exact measurePreserving_snd.comp realImagCoordinates_preserving

omit [Fintype R] [Fintype C] [DecidableEq I] [DecidableEq R] [DecidableEq C] in
theorem pairedComponent_product_preserving (s t : Fin 2) :
    MeasurePreserving (fun z : ((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ) =>
      ((fun i => z.1 (s,i)), (fun i => z.2 (t,i))))
      ((pairedGaussian I).prod (pairedGaussian I))
      ((realGaussianProduct I).prod (realGaussianProduct I)) :=
  (pairedComponent_preserving s).prod (pairedComponent_preserving t)

/-- Complex bilinear chaos in the actual existing CN(0,I) coordinate model. -/
def complexGaussianBilinear (A : I → I → Matrix R C ℂ)
    (x y : (Fin 2 × I) → ℝ) : Matrix R C ℂ :=
  ∑ i, ∑ j, (complexCoordinate x i * star (complexCoordinate y j)) • A i j

omit [Fintype I] [Fintype R] [Fintype C] [DecidableEq I] [DecidableEq R] [DecidableEq C] in
theorem complexCoordinate_mul_star (x y : (Fin 2 × I) → ℝ) (i j : I) :
    complexCoordinate x i * star (complexCoordinate y j) =
      (1/2:ℂ) * ((x (0,i):ℂ)*(y (0,j):ℂ) + (x (1,i):ℂ)*(y (1,j):ℂ) +
        Complex.I*((x (1,i):ℂ)*(y (0,j):ℂ)) - Complex.I*((x (0,i):ℂ)*(y (1,j):ℂ))) := by
  have hs : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
  simp only [complexCoordinate_normalization, star_div₀, star_add, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  field_simp [hs0]
  rw [hs]
  ring_nf
  simp [Complex.I_sq]

omit [Fintype R] [Fintype C] [DecidableEq I] [DecidableEq R] [DecidableEq C] in
theorem complexGaussianBilinear_real_expansion (A : I → I → Matrix R C ℂ)
    (x y : (Fin 2 × I) → ℝ) :
    complexGaussianBilinear A x y = (1/2:ℂ) •
      (gaussianMatrixChaos A (fun i => x (0,i)) (fun i => y (0,i)) +
        gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (1,i)) +
        Complex.I • gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (0,i)) -
        Complex.I • gaussianMatrixChaos A (fun i => x (0,i)) (fun i => y (1,i))) := by
  simp only [complexGaussianBilinear, complexCoordinate_mul_star, gaussianMatrixChaos,
    Finset.smul_sum, smul_add, smul_sub, mul_add, mul_sub, add_smul, sub_smul, smul_smul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

omit [DecidableEq I] [DecidableEq R] in
/-- Each pair of selected real/imaginary components has exactly the independent real law. -/
theorem realComponentChaos_integrable (A : I → I → Matrix R C ℂ) (s t : Fin 2) :
    Integrable (fun z : ((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ) =>
      ‖rectangularEuclideanCLM (gaussianMatrixChaos A (fun i => z.1 (s,i)) (fun i => z.2 (t,i)))‖)
      ((pairedGaussian I).prod (pairedGaussian I)) :=
  (pairedComponent_product_preserving s t).integrable_comp_of_integrable
    (gaussianMatrixChaos_opNorm_integrable A)

omit [DecidableEq I] [DecidableEq R] in
theorem realComponentChaos_integral (A : I → I → Matrix R C ℂ) (s t : Fin 2) :
    (∫ z, ‖rectangularEuclideanCLM
      (gaussianMatrixChaos A (fun i => z.1 (s,i)) (fun i => z.2 (t,i)))‖
      ∂(pairedGaussian I).prod (pairedGaussian I)) =
      ∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
        ∂(realGaussianProduct I).prod (realGaussianProduct I) := by
  have hp := pairedComponent_product_preserving (I := I) s t
  have h := integral_map_of_stronglyMeasurable (μ := (pairedGaussian I).prod (pairedGaussian I)) hp.measurable
    (gaussianMatrixChaos_opNorm_continuous A).stronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm

omit [DecidableEq R] in
/-- Global scalar phases leave all four actual Euclidean flattening norms unchanged. -/
theorem gaussianChaosFlatteningNorm_phase (A : I → I → Matrix R C ℂ) (c : ℂ) (hc : ‖c‖=1) :
    gaussianChaosFlatteningNorm (fun i j => c • A i j) = gaussianChaosFlatteningNorm A := by
  unfold gaussianChaosFlatteningNorm
  have h1 : chaosFlattening₁ (fun i j => c • A i j) = c • chaosFlattening₁ A := rfl
  have h2 : chaosFlattening₂ (fun i j => c • A i j) = c • chaosFlattening₂ A := rfl
  have h3 : chaosFlattening₃ (fun i j => c • A i j) = c • chaosFlattening₃ A := rfl
  have h4 : chaosFlattening₄ (fun i j => c • A i j) = c • chaosFlattening₄ A := rfl
  simp only [h1,h2,h3,h4,rectangularEuclideanCLM_norm,norm_smul,hc,one_mul]

omit [DecidableEq I] [DecidableEq R] in
/-- The normalization 1/sqrt(2) gives one half of four real bilinear series. -/
theorem complexGaussianBilinear_opNorm_le (A : I → I → Matrix R C ℂ)
    (x y : (Fin 2 × I) → ℝ) :
    ‖rectangularEuclideanCLM (complexGaussianBilinear A x y)‖ ≤ (1/2:ℝ) *
      (‖rectangularEuclideanCLM (gaussianMatrixChaos A (fun i => x (0,i)) (fun i => y (0,i)))‖ +
       ‖rectangularEuclideanCLM (gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (1,i)))‖ +
       ‖rectangularEuclideanCLM (gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (0,i)))‖ +
       ‖rectangularEuclideanCLM (gaussianMatrixChaos A (fun i => x (0,i)) (fun i => y (1,i)))‖) := by
  simp only [rectangularEuclideanCLM_norm, complexGaussianBilinear_real_expansion, norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have h1 := norm_sub_le
    (gaussianMatrixChaos A (fun i => x (0,i)) (fun i => y (0,i)) +
      gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (1,i)) +
      Complex.I • gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (0,i)))
    (Complex.I • gaussianMatrixChaos A (fun i => x (0,i)) (fun i => y (1,i)))
  have h2 := norm_add_le
    (gaussianMatrixChaos A (fun i => x (0,i)) (fun i => y (0,i)) +
      gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (1,i)))
    (Complex.I • gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (0,i)))
  have h3 := norm_add_le (gaussianMatrixChaos A (fun i => x (0,i)) (fun i => y (0,i)))
    (gaussianMatrixChaos A (fun i => x (1,i)) (fun i => y (1,i)))
  simp only [norm_smul, Complex.norm_I, one_mul] at h1 h2
  linarith

omit [DecidableEq I] [DecidableEq R] in
theorem complexGaussianBilinear_opNorm_continuous (A : I → I → Matrix R C ℂ) :
    Continuous (fun z : ((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ) =>
      ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)‖) := by
  simp only [rectangularEuclideanCLM, complexGaussianBilinear, map_sum, map_smul]
  unfold complexCoordinate
  fun_prop

omit [DecidableEq I] [DecidableEq R] in
theorem complexGaussianBilinear_opNorm_integrable (A : I → I → Matrix R C ℂ) :
    Integrable (fun z : ((Fin 2 × I) → ℝ) × ((Fin 2 × I) → ℝ) =>
      ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)‖)
      ((pairedGaussian I).prod (pairedGaussian I)) := by
  have he := (((realComponentChaos_integrable A 0 0).add
    (realComponentChaos_integrable A 1 1)).add
    (realComponentChaos_integrable A 1 0)).add (realComponentChaos_integrable A 0 1)
  apply (he.const_mul (1/2:ℝ)).mono' (complexGaussianBilinear_opNorm_continuous A).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_norm] using complexGaussianBilinear_opNorm_le A z.1 z.2

omit [DecidableEq I] [DecidableEq R] in
/-- Four real components cost exactly a factor two before the later centered decoupling step. -/
theorem complexGaussianBilinear_expectation_le_real (A : I → I → Matrix R C ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)‖
      ∂(pairedGaussian I).prod (pairedGaussian I)) ≤
      2 * ∫ z, ‖rectangularEuclideanCLM (gaussianMatrixChaos A z.1 z.2)‖
        ∂(realGaussianProduct I).prod (realGaussianProduct I) := by
  have h00 := realComponentChaos_integrable A 0 0
  have h11 := realComponentChaos_integrable A 1 1
  have h10 := realComponentChaos_integrable A 1 0
  have h01 := realComponentChaos_integrable A 0 1
  have h := integral_mono (complexGaussianBilinear_opNorm_integrable A)
    (((h00.add h11).add h10).add h01 |>.const_mul (1/2:ℝ))
    (fun z => complexGaussianBilinear_opNorm_le A z.1 z.2)
  rw [integral_const_mul] at h
  have hs1 := integral_add ((h00.add h11).add h10) h01
  have hs2 := integral_add (h00.add h11) h10
  have hs3 := integral_add h00 h11
  simp only [Pi.add_apply] at h hs1 hs2 hs3
  rw [hs1, hs2, hs3] at h
  simp only [realComponentChaos_integral] at h
  linarith

/-- The real-Gaussian matrix theorem applied to the actual standard complex Gaussian bilinear form. -/
theorem complexGaussianBilinear_expectation_bound (A : I → I → Matrix R C ℂ) :
    (∫ z, ‖rectangularEuclideanCLM (complexGaussianBilinear A z.1 z.2)‖
      ∂(pairedGaussian I).prod (pairedGaussian I)) ≤
      (2*gaussianMatrixChaosConstant) * Real.sqrt
        (Real.log (2*((Fintype.card R:ℝ)+Fintype.card C)) *
          Real.log (2*(Fintype.card I:ℝ)*((Fintype.card R:ℝ)+Fintype.card C))) *
        gaussianChaosFlatteningNorm A := by
  have h := (complexGaussianBilinear_expectation_le_real A).trans
    (mul_le_mul_of_nonneg_left (gaussianMatrixChaos_expectation_bound A) (by norm_num : (0:ℝ)≤2))
  convert h using 1
  ring

end CertificationGaussian
