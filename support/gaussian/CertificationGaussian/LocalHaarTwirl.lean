import CertificationGaussian.SphereQuadraticMoments
import CertificationGaussian.HaarSymmetricTwirl

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian
/-- The finite square matrices in the Haar model carry the coordinatewise
measurable structure used in its definition of normalized Haar measure. -/
instance (priority := 1100) haarCoordinateMatrixMeasurableSpace (I : Type*) [Fintype I] :
    MeasurableSpace (Matrix I I ℂ) := Matrix.instMeasurableSpace
variable (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I]

/-- The actual standard coordinate unit vector on the complex sphere. -/
def coordinateUnitVector (j : I) : sphere (0 : EuclideanSpace ℂ I) 1 :=
  ⟨EuclideanSpace.basisFun I ℂ j, mem_sphere_zero_iff_norm.mpr
    ((EuclideanSpace.basisFun I ℂ).orthonormal.norm_eq_one j)⟩

omit [Nonempty I] in
theorem complexUnitary_column (U : ComplexUnitary I) (j a : I) :
    (complexUnitarySphereAction I U (coordinateUnitVector I j)).val a = U.val a j := by
  rw [complexUnitarySphereAction_coe]
  simp [coordinateUnitVector, EuclideanSpace.basisFun_apply,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]

/-- Haar averaging of each actual unitary column has the proved complex sphere fourth tensor. -/
theorem haar_column_fourth_moment (j a b c d : I) :
    ∫ U : ComplexUnitary I,
      star (U.val a j)*U.val b j*star (U.val c j)*U.val d j ∂complexUnitaryHaar I =
      ((if a=b then 1 else 0)*(if c=d then 1 else 0) +
       (if a=d then 1 else 0)*(if c=b then 1 else 0)) /
        ((Fintype.card I : ℂ)*((Fintype.card I : ℂ)+1)) := by
  by_cases h : Nontrivial I
  · let _ := h
    exact haar_column_fourth_moment_symmetric _ _ j a b c d
  have h := complexSphere_coordinate_fourth_moment I a b c d
  rw [← complexUnitaryHaar_orbit_map I (coordinateUnitVector I j)] at h
  rw [integral_map (complexUnitarySphereAction_continuous I).measurable.of_uncurry_right.aemeasurable
    (show Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 =>
      star (ψ.val a)*ψ.val b*star (ψ.val c)*ψ.val d) by fun_prop).aestronglyMeasurable] at h
  simpa only [complexUnitary_column] using h

/-- Actual basis dephasing: conjugate into the basis, discard off-diagonal entries, conjugate back. -/
def unitaryDephasing (U : Matrix I I ℂ) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  U * Matrix.diagonal (Matrix.diag (U.conjTranspose*A*U)) * U.conjTranspose

omit [Nonempty I] in
theorem unitaryDephasing_apply (U A : Matrix I I ℂ) (a b : I) :
    unitaryDephasing I U A a b = ∑ j, ∑ c, ∑ d,
      A d c*(star (U b j)*U a j*star (U d j)*U c j) := by
  change (∑ j, (U * Matrix.diagonal (Matrix.diag (U.conjTranspose*A*U))) a j *
    star (U b j)) = _
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

omit [Nonempty I] in
theorem complexUnitaryHaar_integrable_continuous (f : ComplexUnitary I → ℂ)
    (hf : Continuous f) : Integrable f (complexUnitaryHaar I) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [Nonempty I] in
@[fun_prop] theorem complexUnitary_entry_continuous (a b : I) :
    Continuous (fun U : ComplexUnitary I => U.val a b) :=
  (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)

omit [Nonempty I] in
@[fun_prop] theorem unitaryDephasing_entry_continuous (A : Matrix I I ℂ) (a b : I) :
    Continuous (fun U : ComplexUnitary I => unitaryDephasing I U.val A a b) := by
  simp_rw [unitaryDephasing_apply]
  fun_prop

omit [Nonempty I] in
theorem unitaryDephasing_entry_integrable (A : Matrix I I ℂ) (a b : I) :
    Integrable (fun U : ComplexUnitary I => unitaryDephasing I U.val A a b) (complexUnitaryHaar I) :=
  complexUnitaryHaar_integrable_continuous I _ (unitaryDephasing_entry_continuous I A a b)

/-- True full-Haar basis dephasing, for arbitrary complex matrices, with all integrability proved. -/
theorem haar_unitaryDephasing_entry (A : Matrix I I ℂ) (a b : I) :
    ∫ U : ComplexUnitary I, unitaryDephasing I U.val A a b ∂complexUnitaryHaar I =
      (A a b + if a=b then Matrix.trace A else 0)/((Fintype.card I : ℂ)+1) := by
  simp_rw [unitaryDephasing_apply]
  simp (disch := (intro _ _; apply complexUnitaryHaar_integrable_continuous; fun_prop)) only [integral_finsetSum]
  simp_rw [integral_const_mul, haar_column_fourth_moment, ← mul_div_assoc, ← Finset.sum_div]
  have hD : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD1 : (Fintype.card I : ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (Fintype.card I : ℝ)+1 ≠ 0 by positivity)
  simp [mul_add, mul_ite, Finset.sum_add_distrib, Matrix.trace, Matrix.diag]
  by_cases hab : a=b <;> simp [hab, eq_comm]
  all_goals field_simp
  all_goals ring

/-- Rank-one projector of the recorded basis column. -/
def columnProjector (U : Matrix I I ℂ) (j : I) : Matrix I I ℂ :=
  fun a b => U a j*star (U b j)

omit [Nonempty I] in
theorem sum_columnProjector (U : ComplexUnitary I) :
    ∑ j, columnProjector I U.val j = 1 := by
  ext a b
  rw [Matrix.sum_apply]
  change (∑ j, U.val a j*star (U.val b j)) = (1 : Matrix I I ℂ) a b
  have h := congrArg (fun M : Matrix I I ℂ => M a b) U.property.2
  exact h

omit [DecidableEq I] [Nonempty I] in
/-- The recorded overlap is exactly the diagonal after compression by U†. -/
theorem columnProjector_trace (U A : Matrix I I ℂ) (j : I) :
    Matrix.trace (columnProjector I U j*A) = (U.conjTranspose*A*U) j j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, columnProjector,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

omit [Nonempty I] in
/-- Same dephasing channel, retaining every actual basis/outcome projector record. -/
theorem unitaryDephasing_eq_projector_sum (U A : Matrix I I ℂ) :
    unitaryDephasing I U A = ∑ j, Matrix.trace (columnProjector I U j*A) • columnProjector I U j := by
  ext a b
  change (∑ j, (U * Matrix.diagonal (Matrix.diag (U.conjTranspose*A*U))) a j * star (U b j)) = _
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, columnProjector_trace,
    Matrix.diag, columnProjector, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Complement response for the same complete basis/outcome records. -/
def unitaryComplementDephasing (U A : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ j, Matrix.trace ((1-columnProjector I U j)*A) • columnProjector I U j

omit [Nonempty I] in
theorem unitaryComplementDephasing_eq (U : ComplexUnitary I) (A : Matrix I I ℂ) :
    unitaryComplementDephasing I U.val A = Matrix.trace A • (1 : Matrix I I ℂ) -
      unitaryDephasing I U.val A := by
  rw [unitaryComplementDephasing, unitaryDephasing_eq_projector_sum]
  simp only [Matrix.sub_mul, one_mul, Matrix.trace_sub, sub_smul, Finset.sum_sub_distrib]
  rw [← Finset.smul_sum, sum_columnProjector]

/-- Actual complement Haar average on the same basis records. -/
theorem haar_unitaryComplementDephasing_entry (A : Matrix I I ℂ) (a b : I) :
    ∫ U : ComplexUnitary I, unitaryComplementDephasing I U.val A a b ∂complexUnitaryHaar I =
      (((Fintype.card I : ℂ)*Matrix.trace A)*(if a=b then 1 else 0)-A a b) /
        ((Fintype.card I : ℂ)+1) := by
  simp_rw [unitaryComplementDephasing_eq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [integral_sub (integrable_const _) (unitaryDephasing_entry_integrable I A a b),
    integral_const, haar_unitaryDephasing_entry]
  simp only [probReal_univ, one_smul, Matrix.one_apply]
  have hD1 : (Fintype.card I : ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (Fintype.card I : ℝ)+1 ≠ 0 by positivity)
  by_cases hab : a=b <;> simp [hab]
  all_goals field_simp
  all_goals ring

omit [Nonempty I] in
/-- This is exactly the standard coordinate effect compressed by U†, entry for entry. -/
theorem columnProjector_eq_conjugate_single (U : Matrix I I ℂ) (j : I) :
    columnProjector I U j = U*Matrix.single j j (1:ℂ)*U.conjTranspose := by
  ext a b
  simp [columnProjector, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]

omit [Nonempty I] in
theorem unitary_columnProjector_trace (U : ComplexUnitary I) (j : I) :
    Matrix.trace (columnProjector I U.val j) = 1 := by
  have h := congrArg (fun M : Matrix I I ℂ => M j j) U.property.1
  simpa [Matrix.trace, Matrix.diag, columnProjector, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, mul_comm] using h

end CertificationGaussian
