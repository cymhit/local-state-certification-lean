import CertificationGaussian.SphereRealMoments

noncomputable section
open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators ComplexConjugate
namespace CertificationGaussian
variable (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I]

omit [DecidableEq I] [Nonempty I] in
/-- Complex sphere expectations are transported by the already identified canonical-area isometry. -/
theorem complexSphere_integral_eq_real (f : EuclideanSpace ℂ I → ℂ) :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1, f ψ ∂canonicalSphereMeasure (EuclideanSpace ℂ I) =
      ∫ ψ : sphere (0 : EuclideanSpace ℝ (Fin 2 × I)) 1,
        f (complexRealIsometry I ψ) ∂standardSphereMeasure (Fin 2 × I) := by
  rw [← sphereIsometry_canonical_map (complexRealIsometry I)]
  exact (sphereIsometry (complexRealIsometry I)).measurableEmbedding.integral_map _

omit [DecidableEq I] [Nonempty I] in
/-- Unit-sphere real/imaginary coordinates have no further sqrt(2) factor. -/
theorem complexRealIsometry_coordinate (x : EuclideanSpace ℝ (Fin 2 × I)) (i : I) :
    complexRealIsometry I x i = (x (0,i):ℂ)+(x (1,i):ℂ)*Complex.I := by
  have h := congrArg (fun z : EuclideanSpace ℂ I => z i)
    (complexRealIsometry_toLp I (WithLp.ofLp x))
  exact h

omit [DecidableEq I] in
theorem realSphere_complex_integrable (f : sphere (0 : EuclideanSpace ℝ I) 1 → ℂ)
    (hf : Continuous f) : Integrable f (standardSphereMeasure I) := by
  let : CompactSpace (sphere (0 : EuclideanSpace ℝ I) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The covariance of the actual complex canonical sphere. -/
theorem complexSphere_coordinate_second_moment (i j : I) :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
      star (ψ.val i)*ψ.val j ∂canonicalSphereMeasure (EuclideanSpace ℂ I) =
      (if i=j then 1 else 0)/(Fintype.card I : ℂ) := by
  rw [complexSphere_integral_eq_real I (fun x => star (x i)*x j)]
  simp_rw [complexRealIsometry_coordinate]
  have he (x : EuclideanSpace ℝ (Fin 2 × I)) :
      star ((x (0,i):ℂ)+(x (1,i):ℂ)*Complex.I) *
        ((x (0,j):ℂ)+(x (1,j):ℂ)*Complex.I) =
      ((x (0,i)*x (0,j):ℝ):ℂ) + ((x (1,i)*x (1,j):ℝ):ℂ) +
        ((x (0,i)*x (1,j):ℝ):ℂ)*Complex.I - ((x (1,i)*x (0,j):ℝ):ℂ)*Complex.I := by
    simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_mul]
    ring_nf
    simp
  simp_rw [he]
  have hi (f : sphere (0 : EuclideanSpace ℝ (Fin 2 × I)) 1 → ℂ) (hf : Continuous f) :=
    realSphere_complex_integrable (Fin 2 × I) f hf
  rw [integral_sub (hi _ (by fun_prop)) (hi _ (by fun_prop)),
    integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop)),
    integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop))]
  simp_rw [integral_mul_const, integral_complex_ofReal, standardSphere_coordinate_second_moment]
  by_cases hij : i=j <;> simp [hij, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, div_mul_eq_div_mul_one_div]
  ring

/-- The actual complex sphere fourth tensor contracts in exactly the two conjugate pairings. -/
theorem complexSphere_coordinate_fourth_moment (i j k l : I) :
    ∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1,
      star (ψ.val i)*ψ.val j*star (ψ.val k)*ψ.val l
        ∂canonicalSphereMeasure (EuclideanSpace ℂ I) =
      ((if i=j then 1 else 0)*(if k=l then 1 else 0) +
       (if i=l then 1 else 0)*(if k=j then 1 else 0)) /
        ((Fintype.card I : ℂ)*((Fintype.card I : ℂ)+1)) := by
  rw [complexSphere_integral_eq_real I (fun x => star (x i)*x j*star (x k)*x l)]
  let c : Fin 2 → ℂ := fun a => if a=0 then 1 else Complex.I
  have he (x : EuclideanSpace ℝ (Fin 2 × I)) :
      star (complexRealIsometry I x i)*complexRealIsometry I x j*
        star (complexRealIsometry I x k)*complexRealIsometry I x l =
      ∑ a : Fin 2, ∑ b : Fin 2, ∑ e : Fin 2, ∑ d : Fin 2,
        (star (c a)*c b*star (c e)*c d) *
          ((x (a,i)*x (b,j)*x (e,k)*x (d,l) : ℝ):ℂ) := by
    simp only [complexRealIsometry_coordinate, Fin.sum_univ_two, c]
    norm_num [star_add, star_mul, Complex.star_def, Complex.ofReal_mul]
    ring_nf
    norm_num [pow_succ]
    ring
  simp_rw [he]
  have hint (f : sphere (0 : EuclideanSpace ℝ (Fin 2 × I)) 1 → ℂ) (hf : Continuous f) :=
    realSphere_complex_integrable (Fin 2 × I) f hf
  simp (disch := (intro _ _; apply hint; fun_prop)) only [integral_finsetSum]
  simp_rw [integral_const_mul, integral_complex_ofReal, standardSphere_coordinate_fourth_moment]
  simp only [Fin.sum_univ_two, Fintype.card_prod, Fintype.card_fin, c]
  have hD : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD1 : (Fintype.card I : ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (Fintype.card I : ℝ)+1 ≠ 0 by positivity)
  clear he hint
  norm_num [Prod.mk.injEq, Complex.star_def, Nat.cast_mul,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add]
  field_simp
  ring_nf
  simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, eq_comm]

end CertificationGaussian
