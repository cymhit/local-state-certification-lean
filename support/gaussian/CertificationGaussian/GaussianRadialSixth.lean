import CertificationGaussian.GaussianPolynomialIBP
import CertificationGaussian.SphereHomogeneous

noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial Finset
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The true squared Euclidean norm in the original independent real coordinates. -/
def realSquaredNormPolynomial : MvPolynomial I ℝ := ∑ i, (X i)^2

def realGaussianPolynomialExpectation (P : MvPolynomial I ℝ) : ℝ :=
  ∫ x, MvPolynomial.eval x P ∂realGaussianProduct I

omit [DecidableEq I] in
theorem realGaussianPolynomialExpectation_sum {J : Type*} (s : Finset J) (f : J → MvPolynomial I ℝ) :
    realGaussianPolynomialExpectation (∑ j ∈ s, f j) = ∑ j ∈ s, realGaussianPolynomialExpectation (f j) := by
  unfold realGaussianPolynomialExpectation
  simp only [map_sum]
  exact integral_finsetSum s (fun j _ => realGaussianProduct_polynomial_integrable (f j))

omit [DecidableEq I] in
theorem realGaussianPolynomialExpectation_C_mul (c : ℝ) (P : MvPolynomial I ℝ) :
    realGaussianPolynomialExpectation (C c*P)=c*realGaussianPolynomialExpectation P := by
  simp only [realGaussianPolynomialExpectation,map_mul,eval_C,integral_const_mul]

theorem realGaussianPolynomialExpectation_X_mul (i : I) (P : MvPolynomial I ℝ) :
    realGaussianPolynomialExpectation (X i*P)=realGaussianPolynomialExpectation (pderiv i P) := by
  simpa only [realGaussianPolynomialExpectation,map_mul,eval_X] using
    realGaussianProduct_polynomial_ibp P i

omit [DecidableEq I] in
theorem realSquaredNormPolynomial_eval (x : I → ℝ) :
    MvPolynomial.eval x (realSquaredNormPolynomial (I := I)) = ‖WithLp.toLp 2 x‖^2 := by
  simp [realSquaredNormPolynomial,EuclideanSpace.real_norm_sq_eq]

theorem realSquaredNormPolynomial_pderiv (i : I) :
    pderiv i (realSquaredNormPolynomial (I := I)) = 2*X i := by
  simp [realSquaredNormPolynomial,pderiv_X,Pi.single_apply]

omit [DecidableEq I] in
theorem realSquaredNormPolynomial_euler_left :
    (∑ i, X i*(X i*realSquaredNormPolynomial (I := I)^2)) = realSquaredNormPolynomial^3 := by
  have he : (∑ i, X i*(X i*realSquaredNormPolynomial (I := I)^2)) =
      (∑ i : I, (X i)^2)*realSquaredNormPolynomial^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  change realSquaredNormPolynomial*realSquaredNormPolynomial^2=realSquaredNormPolynomial^3
  ring

theorem realSquaredNormPolynomial_euler_derivative :
    (∑ i, pderiv i (X i*realSquaredNormPolynomial (I := I)^2)) =
      C ((Fintype.card I:ℝ)+4)*realSquaredNormPolynomial^2 := by
  have hp (i : I) : pderiv i (X i*realSquaredNormPolynomial (I := I)^2) =
      realSquaredNormPolynomial^2+4*(X i)^2*realSquaredNormPolynomial := by
    simp [realSquaredNormPolynomial_pderiv]
    ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.sum_mul,← Finset.mul_sum]
  change (Fintype.card I: MvPolynomial I ℝ)*realSquaredNormPolynomial^2 +
    4*realSquaredNormPolynomial*realSquaredNormPolynomial = _
  simp only [map_add,map_natCast,map_ofNat]
  ring

/-- Actual integration by parts supplies the radial multiplier m+4, including zero dimension. -/
theorem realSquaredNormPolynomial_third_moment :
    realGaussianPolynomialExpectation (realSquaredNormPolynomial (I := I)^3) =
      ((Fintype.card I:ℝ)+4)*realGaussianPolynomialExpectation (realSquaredNormPolynomial (I := I)^2) := by
  rw [← realSquaredNormPolynomial_euler_left,realGaussianPolynomialExpectation_sum]
  simp_rw [realGaussianPolynomialExpectation_X_mul]
  rw [← realGaussianPolynomialExpectation_sum,realSquaredNormPolynomial_euler_derivative,
    realGaussianPolynomialExpectation_C_mul]

/-- The actual real standard Gaussian radial sixth moment is m(m+2)(m+4). -/
theorem stdGaussian_norm_sixth_moment :
    (∫ x : EuclideanSpace ℝ I, ‖x‖^6 ∂stdGaussian _) =
      (Fintype.card I:ℝ)*((Fintype.card I:ℝ)+2)*((Fintype.card I:ℝ)+4) := by
  have h4 : realGaussianPolynomialExpectation (realSquaredNormPolynomial (I := I)^2) =
      (Fintype.card I:ℝ)*((Fintype.card I:ℝ)+2) := by
    have h := stdGaussian_norm_fourth_moment (I := I)
    rw [stdGaussian_integral_eq_product] at h
    simpa only [realGaussianPolynomialExpectation,map_pow,realSquaredNormPolynomial_eval,
      ← pow_mul,show 2*2=4 by decide] using h
  rw [stdGaussian_integral_eq_product]
  have he : (fun x : I → ℝ => ‖WithLp.toLp 2 x‖^6) =
      (fun x => MvPolynomial.eval x (realSquaredNormPolynomial (I := I)^3)) := by
    funext x
    rw [map_pow,realSquaredNormPolynomial_eval,← pow_mul]
  rw [he]
  change realGaussianPolynomialExpectation (realSquaredNormPolynomial (I := I)^3) = _
  rw [realSquaredNormPolynomial_third_moment,h4]
  ring

end CertificationGaussian
