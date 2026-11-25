import CertificationGaussian.GaussianPolynomialIBP
import CertificationGaussian.Model

noncomputable section
open MeasureTheory MvPolynomial
open scoped BigOperators ENNReal
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Evaluation of an arbitrary complex polynomial in the actual independent standard-real coordinates. -/
def complexCoordinatePolyEval (P : MvPolynomial (Fin 2 × I) ℂ) (x : (Fin 2 × I) → ℝ) : ℂ :=
  MvPolynomial.eval (fun j => (x j:ℂ)) P

/-- The normalized complex coordinate, as a polynomial in the fixed real-coordinate model. -/
def gaussianZPolynomial (i : I) : MvPolynomial (Fin 2 × I) ℂ :=
  C (Real.sqrt 2:ℂ)⁻¹ * (X (0,i) + C Complex.I * X (1,i))

def gaussianBarZPolynomial (i : I) : MvPolynomial (Fin 2 × I) ℂ :=
  C (Real.sqrt 2:ℂ)⁻¹ * (X (0,i) - C Complex.I * X (1,i))

/-- Derivative with respect to the conjugate normalized complex coordinate. -/
def wirtingerBar (i : I) (P : MvPolynomial (Fin 2 × I) ℂ) : MvPolynomial (Fin 2 × I) ℂ :=
  C (Real.sqrt 2:ℂ)⁻¹ * (pderiv (0,i) P + C Complex.I * pderiv (1,i) P)

/-- Derivative with respect to the normalized complex coordinate. -/
def wirtingerZ (i : I) (P : MvPolynomial (Fin 2 × I) ℂ) : MvPolynomial (Fin 2 × I) ℂ :=
  C (Real.sqrt 2:ℂ)⁻¹ * (pderiv (0,i) P - C Complex.I * pderiv (1,i) P)

def complexGaussianPolyExpectation (P : MvPolynomial (Fin 2 × I) ℂ) : ℂ :=
  ∫ x, complexCoordinatePolyEval P x ∂pairedGaussian I

omit [Fintype I] [DecidableEq I] in
theorem complexCoordinatePolyEval_z (i : I) (x : Fin 2 × I → ℝ) :
    complexCoordinatePolyEval (gaussianZPolynomial i) x = complexCoordinate x i := by
  rw [complexCoordinate_normalization]
  simp only [complexCoordinatePolyEval, gaussianZPolynomial, map_mul, map_add, eval_C, eval_X]
  ring

omit [Fintype I] [DecidableEq I] in
theorem complexCoordinatePolyEval_barz (i : I) (x : Fin 2 × I → ℝ) :
    complexCoordinatePolyEval (gaussianBarZPolynomial i) x = star (complexCoordinate x i) := by
  rw [complexCoordinate_normalization]
  simp only [complexCoordinatePolyEval, gaussianBarZPolynomial, map_mul, map_sub, eval_C, eval_X,
    star_div₀, star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

omit [DecidableEq I] in
theorem complexCoordinatePolyEval_memLp (P : MvPolynomial (Fin 2 × I) ℂ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (complexCoordinatePolyEval P) p (pairedGaussian I) :=
  realGaussianProduct_complex_polynomial_memLp P p hp

omit [DecidableEq I] in
theorem complexCoordinatePolyEval_integrable (P : MvPolynomial (Fin 2 × I) ℂ) :
    Integrable (complexCoordinatePolyEval P) (pairedGaussian I) :=
  realGaussianProduct_complex_polynomial_integrable P

omit [DecidableEq I] in
theorem complexGaussianPolyExpectation_add (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (P+Q) = complexGaussianPolyExpectation P+complexGaussianPolyExpectation Q := by
  simpa only [complexGaussianPolyExpectation, complexCoordinatePolyEval, map_add] using
    integral_add (complexCoordinatePolyEval_integrable P) (complexCoordinatePolyEval_integrable Q)

omit [DecidableEq I] in
theorem complexGaussianPolyExpectation_sub (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (P-Q) = complexGaussianPolyExpectation P-complexGaussianPolyExpectation Q := by
  simpa only [complexGaussianPolyExpectation, complexCoordinatePolyEval, map_sub] using
    integral_sub (complexCoordinatePolyEval_integrable P) (complexCoordinatePolyEval_integrable Q)

omit [DecidableEq I] in
theorem complexGaussianPolyExpectation_C_mul (c : ℂ) (P : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (C c*P) = c*complexGaussianPolyExpectation P := by
  unfold complexGaussianPolyExpectation complexCoordinatePolyEval
  simp only [map_mul, eval_C, integral_const_mul]

theorem complexGaussianPolyExpectation_X_mul (j : Fin 2 × I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (X j*P) = complexGaussianPolyExpectation (pderiv j P) := by
  simpa only [complexGaussianPolyExpectation, complexCoordinatePolyEval, map_mul, eval_X,
    realGaussianProduct, pairedGaussian] using
    realGaussianProduct_complex_polynomial_ibp P j

/-- Actual normalized CN integration by parts, no boundedness or hidden moment premise. -/
theorem complexGaussianPolyExpectation_z_ibp (i : I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (gaussianZPolynomial i*P) = complexGaussianPolyExpectation (wirtingerBar i P) := by
  simp only [gaussianZPolynomial, wirtingerBar, mul_assoc, add_mul,
    complexGaussianPolyExpectation_C_mul, complexGaussianPolyExpectation_add,
    complexGaussianPolyExpectation_X_mul]

theorem complexGaussianPolyExpectation_barz_ibp (i : I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (gaussianBarZPolynomial i*P) = complexGaussianPolyExpectation (wirtingerZ i P) := by
  simp only [gaussianBarZPolynomial, wirtingerZ, mul_assoc, sub_mul,
    complexGaussianPolyExpectation_C_mul, complexGaussianPolyExpectation_sub,
    complexGaussianPolyExpectation_X_mul]

/-- Integral form, explicitly using the same z=(ξ+iη)/sqrt 2 as every Gaussian consumer. -/
theorem complexGaussian_z_wirtinger_ibp (i : I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    (∫ x, complexCoordinate x i * complexCoordinatePolyEval P x ∂pairedGaussian I) =
      ∫ x, complexCoordinatePolyEval (wirtingerBar i P) x ∂pairedGaussian I := by
  have h := complexGaussianPolyExpectation_z_ibp i P
  simpa only [complexGaussianPolyExpectation, complexCoordinatePolyEval, map_mul,
    show ∀ x, eval (fun j => (x j:ℂ)) (gaussianZPolynomial i) = complexCoordinate x i from
      complexCoordinatePolyEval_z i] using h

theorem complexGaussian_barz_wirtinger_ibp (i : I) (P : MvPolynomial (Fin 2 × I) ℂ) :
    (∫ x, star (complexCoordinate x i) * complexCoordinatePolyEval P x ∂pairedGaussian I) =
      ∫ x, complexCoordinatePolyEval (wirtingerZ i P) x ∂pairedGaussian I := by
  have h := complexGaussianPolyExpectation_barz_ibp i P
  simpa only [complexGaussianPolyExpectation, complexCoordinatePolyEval, map_mul,
    show ∀ x, eval (fun j => (x j:ℂ)) (gaussianBarZPolynomial i) = star (complexCoordinate x i) from
      complexCoordinatePolyEval_barz i] using h


omit [Fintype I] [DecidableEq I] in
theorem wirtingerBar_add (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    wirtingerBar i (P+Q) = wirtingerBar i P+wirtingerBar i Q := by
  simp only [wirtingerBar, map_add]
  ring

omit [Fintype I] [DecidableEq I] in
theorem wirtingerZ_add (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    wirtingerZ i (P+Q) = wirtingerZ i P+wirtingerZ i Q := by
  simp only [wirtingerZ, map_add]
  ring

omit [Fintype I] [DecidableEq I] in
theorem wirtingerBar_mul (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    wirtingerBar i (P*Q) = wirtingerBar i P*Q+P*wirtingerBar i Q := by
  simp only [wirtingerBar, pderiv_mul]
  ring

omit [Fintype I] [DecidableEq I] in
theorem wirtingerZ_mul (i : I) (P Q : MvPolynomial (Fin 2 × I) ℂ) :
    wirtingerZ i (P*Q) = wirtingerZ i P*Q+P*wirtingerZ i Q := by
  simp only [wirtingerZ, pderiv_mul]
  ring

omit [Fintype I] [DecidableEq I] in
theorem wirtingerBar_C (i : I) (c : ℂ) : wirtingerBar i (C c) = 0 := by
  simp [wirtingerBar]

omit [Fintype I] [DecidableEq I] in
theorem wirtingerZ_C (i : I) (c : ℂ) : wirtingerZ i (C c) = 0 := by
  simp [wirtingerZ]

omit [Fintype I] [DecidableEq I] in
theorem complexPolynomial_I_sq : (C Complex.I : MvPolynomial (Fin 2 × I) ℂ)^2 = -1 := by
  rw [← map_pow]
  norm_num

omit [Fintype I] [DecidableEq I] in
theorem gaussianPolynomial_invSqrt_sq :
    (2 : MvPolynomial (Fin 2 × I) ℂ) * (C (Real.sqrt 2:ℂ)⁻¹)^2 = 1 := by
  have hs : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hc : (2:ℂ) * ((Real.sqrt 2:ℂ)⁻¹)^2 = 1 := by
    have hn : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
    field_simp
    exact hs.symm
  have hp := congrArg (C : ℂ → MvPolynomial (Fin 2 × I) ℂ) hc
  simpa only [map_mul, map_pow, map_ofNat, map_one] using hp

omit [Fintype I] in
/-- Opposite-coordinate derivatives vanish with exact normalized CN scaling. -/
theorem wirtingerBar_z (i j : I) : wirtingerBar i (gaussianZPolynomial j) = 0 := by
  by_cases hij : i=j
  · subst j
    simp [wirtingerBar, gaussianZPolynomial]
    ring_nf
    rw [complexPolynomial_I_sq]
    ring
  · simp [wirtingerBar, gaussianZPolynomial, Ne.symm hij]

omit [Fintype I] in
theorem wirtingerZ_barz (i j : I) : wirtingerZ i (gaussianBarZPolynomial j) = 0 := by
  by_cases hij : i=j
  · subst j
    simp [wirtingerZ, gaussianBarZPolynomial]
    ring_nf
    rw [complexPolynomial_I_sq]
    ring
  · simp [wirtingerZ, gaussianBarZPolynomial, Ne.symm hij]

omit [Fintype I] in
/-- The surviving contraction coefficient is exactly one. -/
theorem wirtingerBar_barz (i j : I) : wirtingerBar i (gaussianBarZPolynomial j) = if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    simp [wirtingerBar, gaussianBarZPolynomial]
    ring_nf
    rw [complexPolynomial_I_sq]
    linear_combination gaussianPolynomial_invSqrt_sq (I := I)
  · simp [wirtingerBar, gaussianBarZPolynomial, hij, Ne.symm hij]

omit [Fintype I] in
theorem wirtingerZ_z (i j : I) : wirtingerZ i (gaussianZPolynomial j) = if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    simp [wirtingerZ, gaussianZPolynomial]
    ring_nf
    rw [complexPolynomial_I_sq]
    linear_combination gaussianPolynomial_invSqrt_sq (I := I)
  · simp [wirtingerZ, gaussianZPolynomial, hij, Ne.symm hij]


omit [Fintype I] [DecidableEq I] in
/-- Finite-product Leibniz rule, retaining each position separately even when coordinate labels repeat. -/
theorem wirtingerZ_prod {J : Type*} [DecidableEq J] (s : Finset J)
    (f : J → MvPolynomial (Fin 2 × I) ℂ) (i : I) :
    wirtingerZ i (∏ j ∈ s, f j) = ∑ j ∈ s, wirtingerZ i (f j) * ∏ k ∈ s.erase j, f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirtingerZ]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, wirtingerZ_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.erase_insert_of_ne (by intro he; subst j; exact ha hj),
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

omit [Fintype I] [DecidableEq I] in
theorem wirtingerBar_prod {J : Type*} [DecidableEq J] (s : Finset J)
    (f : J → MvPolynomial (Fin 2 × I) ℂ) (i : I) :
    wirtingerBar i (∏ j ∈ s, f j) = ∑ j ∈ s, wirtingerBar i (f j) * ∏ k ∈ s.erase j, f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wirtingerBar]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, wirtingerBar_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.erase_insert_of_ne (by intro he; subst j; exact ha hj),
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

omit [DecidableEq I] in
theorem complexGaussianPolyExpectation_C (c : ℂ) : complexGaussianPolyExpectation (C c : MvPolynomial (Fin 2 × I) ℂ) = c := by
  simp [complexGaussianPolyExpectation, complexCoordinatePolyEval, pairedGaussian]

omit [DecidableEq I] in
theorem complexGaussianPolyExpectation_sum {J : Type*} (s : Finset J)
    (f : J → MvPolynomial (Fin 2 × I) ℂ) :
    complexGaussianPolyExpectation (∑ j ∈ s, f j) = ∑ j ∈ s, complexGaussianPolyExpectation (f j) := by
  unfold complexGaussianPolyExpectation complexCoordinatePolyEval
  simp only [map_sum]
  exact integral_finsetSum s (fun j _ => complexCoordinatePolyEval_integrable (f j))

omit [DecidableEq I] in
theorem complexGaussianPolyExpectation_zero : complexGaussianPolyExpectation (0 : MvPolynomial (Fin 2 × I) ℂ) = 0 := by
  simpa only [map_zero] using complexGaussianPolyExpectation_C (I := I) 0

omit [DecidableEq I] in
theorem complexGaussianPolyExpectation_one : complexGaussianPolyExpectation (1 : MvPolynomial (Fin 2 × I) ℂ) = 1 := by
  simpa only [map_one] using complexGaussianPolyExpectation_C (I := I) 1

end CertificationGaussian
