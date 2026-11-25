import CertificationGaussian.GaussianRadialSixth
import CertificationGaussian.ComplexGaussianWick
import CertificationGaussian.SphereComplexMoments

/-! # Even coordinate moments on the complex unit sphere -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Metric Set MvPolynomial
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Gaussian integration by parts for every even radial moment. -/
theorem realSquaredNormPolynomial_moment_succ (k : ℕ) :
    realGaussianPolynomialExpectation (realSquaredNormPolynomial (I := I)^(k+1)) =
      ((Fintype.card I : ℝ) + 2*k) *
        realGaussianPolynomialExpectation (realSquaredNormPolynomial (I := I)^k) := by
  let q := realSquaredNormPolynomial (I := I)
  have he : (∑ i : I, X i * (X i * q^k)) = q^(k+1) := by
    calc
      _ = (∑ i : I, (X i)^2) * q^k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by change q*q^k=q^(k+1); ring
  have hd : (∑ i : I, pderiv i (X i * q^k)) = C ((Fintype.card I:ℝ)+2*k) * q^k := by
    cases k with
    | zero =>
      simp [pderiv_X]
    | succ k =>
      have h (i : I) : pderiv i (X i * q^(k+1)) =
          q^(k+1) + (2 * (k+1) : MvPolynomial I ℝ) * (X i)^2 * q^k := by
        simp [q, realSquaredNormPolynomial_pderiv]
        ring
      simp_rw [h]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      change (Fintype.card I : MvPolynomial I ℝ) * q^(k+1) + 2*(k+1)*q*q^k = _
      simp only [Nat.cast_succ, map_add, map_mul, map_natCast, map_one, map_ofNat]
      ring
  change realGaussianPolynomialExpectation (q^(k+1)) = _
  rw [← he, realGaussianPolynomialExpectation_sum]
  simp_rw [realGaussianPolynomialExpectation_X_mul]
  rw [← realGaussianPolynomialExpectation_sum, hd, realGaussianPolynomialExpectation_C_mul]

/-- For a complex sphere with D coordinates, the real radius contributes
two factors of standard deviation per power and the rising factorial of D. -/
theorem stdGaussian_complexDimension_radial_even (k : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin 2 × I), ‖x‖^(2*k) ∂stdGaussian _) =
      2^k * ((Fintype.card I).ascFactorial k : ℝ) := by
  rw [stdGaussian_integral_eq_product]
  change (∫ x : (Fin 2 × I) → ℝ, ‖WithLp.toLp 2 x‖^(2*k) ∂realGaussianProduct _) = _
  have he (k : ℕ) :
      (∫ x : (Fin 2 × I) → ℝ, ‖WithLp.toLp 2 x‖^(2*k) ∂realGaussianProduct _) =
        realGaussianPolynomialExpectation (realSquaredNormPolynomial (I := Fin 2 × I)^k) := by
    simp only [realGaussianPolynomialExpectation, map_pow, realSquaredNormPolynomial_eval, pow_mul]
  rw [he]
  induction k with
  | zero => simp [realGaussianPolynomialExpectation]
  | succ k ih =>
    rw [realSquaredNormPolynomial_moment_succ, ih, Nat.ascFactorial_succ, pow_succ]
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add]
    ring

/-- The squared modulus of a standard complex normal has factorial moments. -/
theorem complexGaussian_coordinate_even (k : ℕ) (i : I) :
    (∫ x, ‖complexCoordinate x i‖^(2*k) ∂pairedGaussian I) = (k.factorial : ℝ) := by
  have h := complexGaussian_same_coordinate_moment k i
  have he (z : ℂ) : star z^k*z^k = ((‖z‖^(2*k) : ℝ):ℂ) := by
    rw [← mul_pow, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  simp_rw [he] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The k-th moment of the squared modulus of a Haar coordinate. -/
theorem complexSphere_squaredCoordinate_moment [Nonempty I] (k : ℕ) (i : I) :
    (∫ ψ : sphere (0 : EuclideanSpace ℂ I) 1, (‖ψ.val i‖^2)^k
      ∂canonicalSphereMeasure (EuclideanSpace ℂ I)) =
      (k.factorial : ℝ) / ((Fintype.card I).ascFactorial k : ℝ) := by
  have h := gaussian_homogeneous_integral (Fin 2 × I) (2*k)
    (fun x => ‖complexRealIsometry I x i‖^(2*k)) (by
      intro r hr x
      rw [map_smul, PiLp.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow])
  have hcoord (x : (Fin 2 × I) → ℝ) :
      ‖complexRealIsometry I (WithLp.toLp 2 x) i‖^(2*k) =
        2^k * ‖complexCoordinate x i‖^(2*k) := by
    have he := congrArg (fun z : EuclideanSpace ℂ I => z i) (complexGaussianLift_eq I x)
    change complexCoordinate x i = (Real.sqrt 2)⁻¹ • complexRealIsometry I (WithLp.toLp 2 x) i at he
    have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), mul_pow,
      inv_pow, pow_mul (Real.sqrt 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have hgauss : (∫ x : EuclideanSpace ℝ (Fin 2 × I), ‖complexRealIsometry I x i‖^(2*k)
      ∂stdGaussian _) = 2^k * k.factorial := by
    rw [stdGaussian_integral_eq_product]
    simp_rw [hcoord]
    rw [integral_const_mul]
    exact congrArg (fun t : ℝ => 2^k * t) (complexGaussian_coordinate_even k i)
  rw [hgauss, stdGaussian_complexDimension_radial_even] at h
  rw [← sphereIsometry_canonical_map (complexRealIsometry I),
    (sphereIsometry (complexRealIsometry I)).measurableEmbedding.integral_map]
  have hpos : (0:ℝ) < ((Fintype.card I).ascFactorial k : ℝ) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := I))
    rw [hm]
    exact_mod_cast Nat.ascFactorial_pos m k
  apply (eq_div_iff hpos.ne').mpr
  have htwo : (0:ℝ) < 2^k := by positivity
  apply mul_left_cancel₀ htwo.ne'
  change 2^k * ((∫ ψ : sphere (0 : EuclideanSpace ℝ (Fin 2 × I)) 1,
    (‖complexRealIsometry I ψ.val i‖^2)^k ∂standardSphereMeasure (Fin 2 × I)) *
    ((Fintype.card I).ascFactorial k : ℝ)) = _
  rw [← mul_assoc, mul_comm (2^k) _, mul_assoc]
  simp only [pow_mul] at h
  simpa only [mul_comm, mul_assoc, mul_left_comm] using h.symm

end CertificationGaussian

