import CertificationGaussian.SphereQuadraticMoments
import CertificationGaussian.MatrixHermitianDilation
import CertificationGaussian.UnitaryNet

noncomputable section
open Matrix Finset MeasureTheory Metric Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

/-- The genuine orbit matrix, whose column w is W_w ψ. -/
def unitaryOrbitMatrix (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) : Matrix I K ℂ :=
  fun i w => Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (W w) ψ i

def unitaryOrbitGram (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) : Matrix K K ℂ :=
  (unitaryOrbitMatrix W ψ)ᴴ * unitaryOrbitMatrix W ψ

def unitaryOrbitGramError (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) : Matrix K K ℂ :=
  unitaryOrbitGram W ψ - 1

omit [DecidableEq K] [Fintype K] in
theorem unitaryOrbitGram_apply (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) (w v : K) :
    unitaryOrbitGram W ψ w v = inner ℂ
      (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (W w) ψ)
      (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (W v) ψ) := by
  simp only [unitaryOrbitGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    unitaryOrbitMatrix, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq K] [Fintype K] in
theorem unitaryOrbitGram_quadratic (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) (w v : K) :
    unitaryOrbitGram W ψ w v = sphereQuadraticForm ((W w)ᴴ * W v) ψ := by
  rw [unitaryOrbitGram_apply, sphereQuadraticForm_eq_inner, map_mul]
  change inner ℂ _ _ = inner ℂ ψ
    ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (star (W w)))
      (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (W v) ψ))
  rw [map_star]
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

omit [DecidableEq K] [Fintype K] in
theorem unitaryOrbitGram_diagonal (W : K → Matrix I I ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) (w : K) : unitaryOrbitGram W ψ w w = 1 := by
  rw [unitaryOrbitGram_quadratic, show (W w)ᴴ * W w = 1 from (hW w).1,
    sphereQuadraticForm_eq_inner, map_one]
  change inner ℂ (ψ : EuclideanSpace ℂ I) ψ = 1
  rw [inner_self_eq_norm_sq_to_K, mem_sphere_zero_iff_norm.mp ψ.property]
  norm_num

omit [Fintype K] in
theorem unitaryOrbitGramError_apply (W : K → Matrix I I ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) (w v : K) :
    unitaryOrbitGramError W ψ w v = if w=v then 0 else sphereQuadraticForm ((W w)ᴴ*W v) ψ := by
  by_cases hwv : w=v
  · subst v
    simp [unitaryOrbitGramError, unitaryOrbitGram_diagonal W hW ψ]
  · simp [unitaryOrbitGramError, hwv, unitaryOrbitGram_quadratic]

/-- The explicit sum of entrywise squared norms, exactly the squared Frobenius error. -/
def unitaryOrbitGramSquareSum (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) : ℝ :=
  ∑ w, ∑ v, ‖unitaryOrbitGramError W ψ w v‖^2

omit [Fintype K] in
@[fun_prop] theorem unitaryOrbitGramError_continuous (W : K → Matrix I I ℂ) :
    Continuous (unitaryOrbitGramError W) := by
  unfold unitaryOrbitGramError unitaryOrbitGram unitaryOrbitMatrix
  fun_prop

@[fun_prop] theorem unitaryOrbitGramSquareSum_continuous (W : K → Matrix I I ℂ) :
    Continuous (unitaryOrbitGramSquareSum W) := by
  unfold unitaryOrbitGramSquareSum
  fun_prop

theorem unitaryOrbitGramSquareSum_nonneg (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) :
    0 ≤ unitaryOrbitGramSquareSum W ψ :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [DecidableEq I] in
theorem sphere_real_continuous_integrable [Nonempty I]
    (f : sphere (0 : EuclideanSpace ℂ I) 1 → ℝ) (hf : Continuous f) :
    Integrable f (canonicalSphereMeasure (EuclideanSpace ℂ I)) := by
  let : CompactSpace (sphere (0 : EuclideanSpace ℂ I) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [Fintype K] in
theorem unitaryOrbitGramError_entry_moment [Nonempty I] (W : K → Matrix I I ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0)
    (w v : K) :
    (∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1, ‖unitaryOrbitGramError W ψ w v‖^2
      ∂canonicalSphereMeasure (EuclideanSpace ℂ I)) =
        if w=v then 0 else ((Fintype.card I:ℝ)+1)⁻¹ := by
  simp_rw [unitaryOrbitGramError_apply W hW]
  by_cases hwv : w=v
  · simp [hwv]
  · simp only [hwv, ite_false, ← Complex.normSq_eq_norm_sq]
    rw [sphereQuadraticForm_normSq_moment, hHS]
    simp only [hwv, ite_false]
    have hU : (W w)ᴴ * W v ∈ unitary (Matrix I I ℂ) :=
      (unitary (Matrix I I ℂ)).mul_mem (Unitary.star_mem (hW w)) (hW v)
    rw [show ((W w)ᴴ*W v) * ((W w)ᴴ*W v)ᴴ = 1 from hU.2]
    simp only [map_zero, zero_add, Matrix.trace_one, Complex.natCast_re]
    have hD : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp


/-- Exact Frobenius-squared expectation for the actual orbit Gram matrix. -/
theorem unitaryOrbitGramSquareSum_moment [Nonempty I] (W : K → Matrix I I ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    (∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1, unitaryOrbitGramSquareSum W ψ
      ∂canonicalSphereMeasure (EuclideanSpace ℂ I)) =
        (Fintype.card K:ℝ)*((Fintype.card K:ℝ)-1)/((Fintype.card I:ℝ)+1) := by
  change (∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
    ∑ w, ∑ v, ‖unitaryOrbitGramError W ψ w v‖^2 ∂canonicalSphereMeasure (EuclideanSpace ℂ I)) = _
  rw [integral_finsetSum (f := fun (w : K) (ψ : sphere (0 : EuclideanSpace ℂ I) 1) =>
    ∑ v, ‖unitaryOrbitGramError W ψ w v‖^2) Finset.univ
    (fun _ _ => sphere_real_continuous_integrable _ (by fun_prop))]
  have hi (w : K) := integral_finsetSum
    (μ := canonicalSphereMeasure (EuclideanSpace ℂ I))
    (f := fun (v : K) (ψ : sphere (0 : EuclideanSpace ℂ I) 1) =>
      ‖unitaryOrbitGramError W ψ w v‖^2) Finset.univ
    (fun _ _ => sphere_real_continuous_integrable _ (by fun_prop))
  simp_rw [hi, unitaryOrbitGramError_entry_moment W hW hHS]
  have hite (w v : K) : (if w=v then (0:ℝ) else ((Fintype.card I:ℝ)+1)⁻¹) =
      ((Fintype.card I:ℝ)+1)⁻¹ - if w=v then ((Fintype.card I:ℝ)+1)⁻¹ else 0 := by
    by_cases h : w=v <;> simp [h]
  simp_rw [hite, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

theorem unitaryOrbitGramError_norm_sq_le (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) :
    ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ) (unitaryOrbitGramError W ψ)‖^2 ≤
      unitaryOrbitGramSquareSum W ψ := by
  have h := matrix_operator_norm_le_entry_sqrt (unitaryOrbitGramError W ψ)
  have hs := Real.sq_sqrt (unitaryOrbitGramSquareSum_nonneg W ψ)
  change ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ) (unitaryOrbitGramError W ψ)‖ ≤
    Real.sqrt (unitaryOrbitGramSquareSum W ψ) at h
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ) (unitaryOrbitGramError W ψ))]


open scoped Matrix.Norms.Frobenius in
/-- The explicit error sum is precisely the usual Frobenius norm squared. -/
theorem unitaryOrbitGramError_frobenius_sq (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) :
    ‖unitaryOrbitGramError W ψ‖^2 = unitaryOrbitGramSquareSum W ψ := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (unitaryOrbitGramSquareSum_nonneg W ψ)

theorem unitaryOrbitGram_bad_measurable (W : K → Matrix I I ℂ) (t : ℝ) :
    MeasurableSet {ψ : sphere (0 : EuclideanSpace ℂ I) 1 |
      t < ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ) (unitaryOrbitGramError W ψ)‖} := by
  apply isOpen_lt continuous_const ?_ |>.measurableSet
  exact ((Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp
    ((unitaryOrbitGramError_continuous W).comp continuous_subtype_val)).norm

/-- The true operator-norm bad event has the paper's exact m(m-1)/((D+1)t²) bound. -/
theorem unitaryOrbitGram_sphere_tail [Nonempty I] (W : K → Matrix I I ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0)
    (t : ℝ) (ht : 0<t) :
    canonicalSphereMeasure (EuclideanSpace ℂ I)
      {ψ | t < ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ) (unitaryOrbitGramError W ψ)‖} ≤
      ENNReal.ofReal ((Fintype.card K:ℝ)*((Fintype.card K:ℝ)-1)/(((Fintype.card I:ℝ)+1)*t^2)) := by
  have hsub : {ψ : sphere (0 : EuclideanSpace ℂ I) 1 |
      t < ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ) (unitaryOrbitGramError W ψ)‖} ⊆
      {ψ | t^2 ≤ unitaryOrbitGramSquareSum W ψ} := by
    intro ψ hψ
    exact (pow_le_pow_left₀ ht.le hψ.le 2).trans (unitaryOrbitGramError_norm_sq_le W ψ)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := canonicalSphereMeasure (EuclideanSpace ℂ I))
    (f := fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 => unitaryOrbitGramSquareSum W ψ)
    (Filter.Eventually.of_forall (fun ψ => unitaryOrbitGramSquareSum_nonneg W ψ))
    (sphere_real_continuous_integrable _ (by fun_prop)) (t^2)
  rw [unitaryOrbitGramSquareSum_moment W hW hHS] at hmark
  have hreal : (canonicalSphereMeasure (EuclideanSpace ℂ I)).real
      {ψ | t < ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ) (unitaryOrbitGramError W ψ)‖} ≤
      (Fintype.card K:ℝ)*((Fintype.card K:ℝ)-1)/(((Fintype.card I:ℝ)+1)*t^2) := by
    calc
      _ ≤ (canonicalSphereMeasure (EuclideanSpace ℂ I)).real
          {ψ : sphere (0 : EuclideanSpace ℂ I) 1 | t^2 ≤ unitaryOrbitGramSquareSum W ψ} := measureReal_mono hsub
      _ ≤ ((Fintype.card K:ℝ)*((Fintype.card K:ℝ)-1)/((Fintype.card I:ℝ)+1))/(t^2) :=
        (le_div_iff₀ (sq_pos_of_pos ht)).mpr (by simpa only [mul_comm] using hmark)
      _ = _ := div_div _ _ _
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The same Gram event under independently defined full complex-unitary Haar sampling. -/
theorem unitaryOrbitGram_haar_tail [Nonempty I] (W : K → Matrix I I ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0)
    (t : ℝ) (ht : 0<t) (ψ₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    complexUnitaryHaar I
      {U | t < ‖Matrix.toEuclideanCLM (n := K) (𝕜 := ℂ)
        (unitaryOrbitGramError W (complexUnitarySphereAction I U ψ₀))‖} ≤
      ENNReal.ofReal ((Fintype.card K:ℝ)*((Fintype.card K:ℝ)-1)/(((Fintype.card I:ℝ)+1)*t^2)) := by
  have h := unitaryOrbitGram_sphere_tail W hW hHS t ht
  rw [← complexUnitaryHaar_orbit_map I ψ₀,
    Measure.map_apply (complexUnitarySphereAction_continuous I).measurable.of_uncurry_right
      (unitaryOrbitGram_bad_measurable W t)] at h
  exact h


/-- Exact error moment under a genuine full-Haar orbit from any fixed initial unit vector. -/
theorem unitaryOrbitGramSquareSum_haar_moment [Nonempty I] (W : K → Matrix I I ℂ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    (∫ U, unitaryOrbitGramSquareSum W (complexUnitarySphereAction I U ψ₀) ∂complexUnitaryHaar I) =
      (Fintype.card K:ℝ)*((Fintype.card K:ℝ)-1)/((Fintype.card I:ℝ)+1) := by
  have h := unitaryOrbitGramSquareSum_moment W hW hHS
  rw [← complexUnitaryHaar_orbit_map I ψ₀] at h
  rw [integral_map (complexUnitarySphereAction_continuous I).measurable.of_uncurry_right.aemeasurable
    (show Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 =>
      unitaryOrbitGramSquareSum W ψ) by fun_prop).aestronglyMeasurable] at h
  exact h

end CertificationGaussian
