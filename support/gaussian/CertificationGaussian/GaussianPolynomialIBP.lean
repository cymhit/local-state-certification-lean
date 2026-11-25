import CertificationGaussian.GaussianWick4
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal
namespace CertificationGaussian

/-- Every ordinary polynomial is integrable for the actual standard Gaussian. -/
theorem standardGaussian_polynomial_integrable (P : ℝ[X]) :
    Integrable (fun x : ℝ => P.eval x) (gaussianReal 0 1) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.eval_add]
    exact hP.add hQ
  | monomial n a => simpa only [Polynomial.eval_monomial] using
      (standardGaussian_integrable_pow n).const_mul a

/-- Integrability after writing the Gaussian as its actual Lebesgue density. -/
theorem standardGaussian_polynomial_density_integrable (P : ℝ[X]) :
    Integrable (fun x : ℝ => P.eval x * gaussianPDFReal 0 1 x) := by
  have h := standardGaussian_polynomial_integrable P
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)] at h
  have h' := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))).mp h
  simpa only [toReal_gaussianPDF, smul_eq_mul, mul_comm] using h'

private theorem standardGaussian_density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt (fun t : ℝ => -(t^2/2)) (-x) x := by
    convert ((hasDerivAt_pow 2 x).div_const 2).neg using 1; ring
  change HasDerivAt (fun t => gaussianPDFReal 0 1 t) _ _
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, neg_div]
  convert h.exp.const_mul (Real.sqrt (2*Real.pi))⁻¹ using 1
  ring


/-- Gaussian integration by parts for an arbitrary-degree polynomial, with its actual derivative.
The proof uses the density derivative and integrable Lebesgue integration by parts; no boundedness
assumption on the polynomial or its derivative is imposed. -/
theorem standardGaussian_polynomial_ibp (P : ℝ[X]) :
    ∫ x : ℝ, x * P.eval x ∂gaussianReal 0 1 =
      ∫ x : ℝ, P.derivative.eval x ∂gaussianReal 0 1 := by
  have hder (x : ℝ) : deriv (gaussianPDFReal 0 1) x = -x*gaussianPDFReal 0 1 x :=
    (standardGaussian_density_hasDerivAt x).deriv
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (𝕜 := ℝ) (E := ℝ) (μ := volume) (f := fun x => P.eval x)
    (g := gaussianPDFReal 0 1) (v := (1:ℝ))
    ?_ ?_ ?_ (fun x _ => P.differentiable.differentiableAt)
    (fun x _ => (standardGaussian_density_hasDerivAt x).differentiableAt)
  · simp only [fderiv_apply_one_eq_deriv, Polynomial.deriv, hder] at h
    rw [integral_gaussianReal_eq_integral_smul (by norm_num),
      integral_gaussianReal_eq_integral_smul (by norm_num)]
    simp only [smul_eq_mul]
    have he (x : ℝ) : P.eval x*(-x*gaussianPDFReal 0 1 x) =
        -(gaussianPDFReal 0 1 x*(x*P.eval x)) := by ring
    simp_rw [he, integral_neg] at h
    have := neg_injective h
    simpa only [mul_comm] using this
  · simpa only [fderiv_apply_one_eq_deriv, Polynomial.deriv] using
      standardGaussian_polynomial_density_integrable P.derivative
  · simp only [fderiv_apply_one_eq_deriv, hder]
    convert standardGaussian_polynomial_density_integrable (P * (-Polynomial.X)) using 1
    funext x
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_X]
    ring
  · exact standardGaussian_polynomial_density_integrable P

/-- The all-orders Gaussian moment recurrence, including the zero exponent. -/
theorem standardGaussian_moment_recurrence (n : Nat) :
    ∫ x : ℝ, x^(n+1) ∂gaussianReal 0 1 =
      (n:ℝ)*(∫ x : ℝ, x^(n-1) ∂gaussianReal 0 1) := by
  have h := standardGaussian_polynomial_ibp (Polynomial.X^n)
  simpa [Polynomial.derivative_X_pow, pow_succ, mul_comm, integral_const_mul] using h

section FiniteCoordinates
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
private theorem eval_monomial_fintype (s : I →₀ Nat) (a : ℝ) (x : I → ℝ) :
    MvPolynomial.eval x (MvPolynomial.monomial s a) = a * ∏ i, x i^(s i) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

omit [DecidableEq I] in
/-- Every finite-coordinate polynomial is integrable, without a degree bound. -/
theorem realGaussianProduct_polynomial_integrable (P : MvPolynomial I ℝ) :
    Integrable (fun x => MvPolynomial.eval x P) (realGaussianProduct I) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | monomial s a =>
    simp only [eval_monomial_fintype]
    exact (Integrable.fintype_prod (fun i => standardGaussian_integrable_pow (s i))).const_mul a

omit [DecidableEq I] in
private theorem realGaussianProduct_monomial_integral (s : I →₀ Nat) (a : ℝ) :
    ∫ x, MvPolynomial.eval x (MvPolynomial.monomial s a) ∂realGaussianProduct I =
      a * ∏ i, ∫ t : ℝ, t^(s i) ∂gaussianReal 0 1 := by
  simp only [eval_monomial_fintype, integral_const_mul]
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => t^(s i))]

omit [Fintype I] in
/-- Formal partial differentiation is the actual analytic derivative along a coordinate line. -/
theorem polynomial_hasDerivAt_coordinate (P : MvPolynomial I ℝ) (i : I) (x : I → ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update x i t) P)
      (MvPolynomial.eval x (MvPolynomial.pderiv i P)) (x i) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (x i) a
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P j hP =>
    by_cases hji : j = i
    · subst j
      simpa [MvPolynomial.pderiv_mul, Function.update_eq_self, mul_comm, add_comm,
        Pi.mul_apply, id_eq] using! hP.mul (hasDerivAt_id (x i))
    · simpa [MvPolynomial.pderiv_mul, Function.update_of_ne hji,
        Function.update_eq_self, hji, mul_comm] using! hP.mul_const (x j)

/-- Coordinate Gaussian integration by parts for an arbitrary finite-dimensional polynomial. -/
theorem realGaussianProduct_polynomial_ibp (P : MvPolynomial I ℝ) (i : I) :
    ∫ x, x i * MvPolynomial.eval x P ∂realGaussianProduct I =
      ∫ x, MvPolynomial.eval x (MvPolynomial.pderiv i P) ∂realGaussianProduct I := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    have hiP : Integrable (fun x => x i*MvPolynomial.eval x P) (realGaussianProduct I) := by
      convert realGaussianProduct_polynomial_integrable (MvPolynomial.X i*P) using 1
      funext x
      simp
    have hiQ : Integrable (fun x => x i*MvPolynomial.eval x Q) (realGaussianProduct I) := by
      convert realGaussianProduct_polynomial_integrable (MvPolynomial.X i*Q) using 1
      funext x
      simp
    simp only [map_add, mul_add]
    rw [integral_add hiP hiQ,
      integral_add (realGaussianProduct_polynomial_integrable _)
        (realGaussianProduct_polynomial_integrable _), hP, hQ]
  | monomial s a =>
    have he (x : I → ℝ) : x i*MvPolynomial.eval x (MvPolynomial.monomial s a) =
        MvPolynomial.eval x (MvPolynomial.monomial (s+Finsupp.single i 1) a) := by
      rw [← MvPolynomial.eval_X (f := x) i, ← map_mul]
      simp [MvPolynomial.X, add_comm]
    simp_rw [he]
    rw [MvPolynomial.pderiv_monomial, realGaussianProduct_monomial_integral,
      realGaussianProduct_monomial_integral]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply]
    rw [standardGaussian_moment_recurrence]
    have hp : (∏ j ∈ Finset.univ.erase i, ∫ t : ℝ,
        t ^ (s j + Finsupp.single i 1 j) ∂gaussianReal 0 1) =
      ∏ j ∈ Finset.univ.erase i, ∫ t : ℝ,
        t ^ (s j - Finsupp.single i 1 j) ∂gaussianReal 0 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hp]
    ring

omit [DecidableEq I] in
/-- Every finite Gaussian polynomial has all finite moments; this includes exponent zero. -/
theorem realGaussianProduct_polynomial_memLp (P : MvPolynomial I ℝ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => MvPolynomial.eval x P) p (realGaussianProduct I) := by
  let n : Nat := Nat.ceil p.toReal + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hi := realGaussianProduct_polynomial_integrable (P^(2*n))
  have hnorm : Integrable (fun x => ‖MvPolynomial.eval x P‖ ^ (2*n))
      (realGaussianProduct I) := by
    simpa only [map_pow, Real.norm_eq_abs, even_two.mul_right n |>.pow_abs] using hi
  have hq : MemLp (fun x => MvPolynomial.eval x P) (2*n : Nat) (realGaussianProduct I) := by
    apply (integrable_norm_rpow_iff P.continuous_eval.aestronglyMeasurable
      (by exact_mod_cast (by omega : 2*n ≠ 0)) (by finiteness)).mp
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using hnorm
  apply hq.mono_exponent
  apply (ENNReal.toReal_le_toReal hp (by finiteness)).mp
  simp only [ENNReal.toReal_natCast]
  have hceil := Nat.le_ceil p.toReal
  dsimp [n]
  push_cast
  linarith

omit [DecidableEq I] in
private theorem complex_eval_monomial_real (s : I →₀ Nat) (a : ℂ) (x : I → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.monomial s a) =
      a * (MvPolynomial.eval x (MvPolynomial.monomial s (1:ℝ)) : ℂ) := by
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    one_mul, Complex.ofReal_prod, Complex.ofReal_pow]

omit [DecidableEq I] in
/-- Arbitrary complex coefficients are allowed, with all coordinates still standard real Gaussians. -/
theorem realGaussianProduct_complex_polynomial_memLp (P : MvPolynomial I ℂ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : I → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) P)
      p (realGaussianProduct I) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | monomial s a =>
    simp only [complex_eval_monomial_real]
    exact (realGaussianProduct_polynomial_memLp (MvPolynomial.monomial s 1) p hp).ofReal.const_mul a

omit [DecidableEq I] in
/-- In particular all complex polynomial entries and all their partial derivatives are integrable. -/
theorem realGaussianProduct_complex_polynomial_integrable (P : MvPolynomial I ℂ) :
    Integrable (fun x : I → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) P)
      (realGaussianProduct I) :=
  (realGaussianProduct_complex_polynomial_memLp P 1 (by simp)).integrable (by rfl)

omit [DecidableEq I] in
private theorem complex_monomial_integral (s : I →₀ Nat) (a : ℂ) :
    ∫ x : I → ℝ, MvPolynomial.eval (fun i => (x i : ℂ))
      (MvPolynomial.monomial s a) ∂realGaussianProduct I =
      a * (∏ i, ∫ t : ℝ, t^(s i) ∂gaussianReal 0 1 : ℝ) := by
  simp only [complex_eval_monomial_real, integral_const_mul, integral_complex_ofReal,
    realGaussianProduct_monomial_integral, one_mul]

/-- Complex-valued Gaussian integration by parts, with no Hermitian/reality restriction on coefficients. -/
theorem realGaussianProduct_complex_polynomial_ibp (P : MvPolynomial I ℂ) (i : I) :
    ∫ x : I → ℝ, (x i : ℂ) * MvPolynomial.eval (fun j => (x j : ℂ)) P
      ∂realGaussianProduct I =
      ∫ x : I → ℝ, MvPolynomial.eval (fun j => (x j : ℂ)) (MvPolynomial.pderiv i P)
        ∂realGaussianProduct I := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    have hiP : Integrable (fun x : I → ℝ => (x i : ℂ)*MvPolynomial.eval (fun j => (x j : ℂ)) P)
        (realGaussianProduct I) := by
      convert realGaussianProduct_complex_polynomial_integrable (MvPolynomial.X i*P) using 1
      funext x
      simp
    have hiQ : Integrable (fun x : I → ℝ => (x i : ℂ)*MvPolynomial.eval (fun j => (x j : ℂ)) Q)
        (realGaussianProduct I) := by
      convert realGaussianProduct_complex_polynomial_integrable (MvPolynomial.X i*Q) using 1
      funext x
      simp
    simp only [map_add, mul_add]
    rw [integral_add hiP hiQ,
      integral_add (realGaussianProduct_complex_polynomial_integrable _)
        (realGaussianProduct_complex_polynomial_integrable _), hP, hQ]
  | monomial s a =>
    have he (x : I → ℝ) : (x i : ℂ)*MvPolynomial.eval (fun j => (x j : ℂ))
        (MvPolynomial.monomial s a) = MvPolynomial.eval (fun j => (x j : ℂ))
        (MvPolynomial.monomial (s+Finsupp.single i 1) a) := by
      rw [← MvPolynomial.eval_X (f := fun j => (x j : ℂ)) i, ← map_mul]
      simp [MvPolynomial.X, add_comm]
    simp_rw [he]
    rw [MvPolynomial.pderiv_monomial, complex_monomial_integral, complex_monomial_integral]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply]
    rw [standardGaussian_moment_recurrence]
    have hp : (∏ j ∈ Finset.univ.erase i, ∫ t : ℝ,
        t ^ (s j + Finsupp.single i 1 j) ∂gaussianReal 0 1) =
      ∏ j ∈ Finset.univ.erase i, ∫ t : ℝ,
        t ^ (s j - Finsupp.single i 1 j) ∂gaussianReal 0 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hp]
    push_cast
    ring

omit [Fintype I] in
/-- The complex polynomial's formal partial derivative is its actual real coordinate derivative. -/
theorem complex_polynomial_hasDerivAt_coordinate (P : MvPolynomial I ℂ)
    (i : I) (x : I → ℝ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (fun j => (Function.update x i t j : ℂ)) P)
      (MvPolynomial.eval (fun j => (x j : ℂ)) (MvPolynomial.pderiv i P)) (x i) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (x i) a
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P j hP =>
    by_cases hji : j = i
    · subst j
      have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 (x i) := by
        exact (Complex.ofRealCLM.hasFDerivAt (x := x i)).hasDerivAt
      simpa [MvPolynomial.pderiv_mul, Function.update_eq_self, mul_comm, add_comm,
        Pi.mul_apply] using! hP.mul hid
    · simpa [MvPolynomial.pderiv_mul, Function.update_of_ne hji,
        Function.update_eq_self, hji, mul_comm] using! hP.mul_const (x j : ℂ)

end FiniteCoordinates
end CertificationGaussian
