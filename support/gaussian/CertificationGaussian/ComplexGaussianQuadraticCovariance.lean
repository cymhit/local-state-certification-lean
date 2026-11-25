import CertificationGaussian.ComplexGaussianNormalMatrix
import CertificationGaussian.ComplexGaussianMatrixWick
import Mathlib.Probability.Moments.Covariance

/-! # Centered complex Gaussian quadratic moments

The matrix inputs need not commute or be Hermitian. The Hermitian specialization
provides the noncommuting covariance used in Supplemental Material Section IV (quadratic covariance).
-/

noncomputable section
open MeasureTheory MvPolynomial Finset Matrix
open scoped BigOperators ENNReal
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- One centered quadratic coordinate, with its actual Gaussian contraction. -/
def gaussianCenteredCoordinatePolynomial (i j : I) : MvPolynomial (Fin 2 × I) ℂ :=
  gaussianBarZPolynomial i * gaussianZPolynomial j - gaussianDeltaPolynomial i j

/-- The centered matrix quadratic form in the original real Gaussian coordinates. -/
def gaussianCenteredQuadraticPolynomial (A : Matrix I I ℂ) :
    MvPolynomial (Fin 2 × I) ℂ :=
  gaussianMatrixQuadraticPolynomial A - C A.trace

theorem gaussianCenteredQuadraticPolynomial_entries (A : Matrix I I ℂ) :
    gaussianCenteredQuadraticPolynomial A =
      ∑ i, ∑ j, C (A i j) * gaussianCenteredCoordinatePolynomial i j := by
  have hd : (∑ i, ∑ j, C (A i j) * gaussianDeltaPolynomial i j) = C A.trace := by
    simp [gaussianDeltaPolynomial, apply_ite, Matrix.trace, Matrix.diag]
  simp only [gaussianCenteredCoordinatePolynomial, mul_sub, Finset.sum_sub_distrib, hd]
  simp only [gaussianCenteredQuadraticPolynomial, gaussianMatrixQuadraticPolynomial, mul_assoc]

omit [DecidableEq I] in
theorem gaussianCenteredQuadraticPolynomial_eval (A : Matrix I I ℂ)
    (x : Fin 2 × I → ℝ) :
    complexCoordinatePolyEval (gaussianCenteredQuadraticPolynomial A) x =
      sphereQuadraticForm A (WithLp.toLp 2 (complexCoordinate x)) - A.trace := by
  rw [gaussianCenteredQuadraticPolynomial]
  simp only [complexCoordinatePolyEval, map_sub, eval_C,
    show eval (fun c => (x c : ℂ)) (gaussianMatrixQuadraticPolynomial A) =
      sphereQuadraticForm A (WithLp.toLp 2 (complexCoordinate x)) from
      gaussianMatrixQuadraticPolynomial_eval A x]

omit [Fintype I] in
private theorem singleton_normal_block_four (i j : Fin 4 → I) (b : Fin 4) :
    gaussianNormalBlock 4 4 id id i j b = gaussianCenteredCoordinatePolynomial (i b) (j b) := by
  fin_cases b <;>
    simp [gaussianNormalBlock, gaussianBarCreation,
      wirtingerZ_z, gaussianCenteredCoordinatePolynomial, gaussianDeltaPolynomial]

omit [Fintype I] in
private theorem singleton_normal_product_four (i j : Fin 4 → I) :
    gaussianNormalProduct 4 4 id id i j =
      ∏ a, gaussianCenteredCoordinatePolynomial (i a) (j a) := by
  simp only [gaussianNormalProduct, singleton_normal_block_four]

omit [DecidableEq I] in
private theorem gaussianNormalProduct_zero {B : Type*} [Fintype B] [DecidableEq B]
    (c e : Fin 0 → B) (i j : Fin 0 → I) :
    complexGaussianPolyExpectation (gaussianNormalProduct 0 0 c e i j) = 1 := by
  simp [gaussianNormalProduct, gaussianNormalBlock, complexGaussianPolyExpectation_one]

private theorem centeredCoordinate_fourth_pairings (i j : Fin 4 → I) :
    complexGaussianPolyExpectation (∏ a, gaussianCenteredCoordinatePolynomial (i a) (j a)) =
      complexGaussianBlockPairingSum 4 (id : Fin 4 → Fin 4) id i j := by
  rw [← singleton_normal_product_four]
  exact complexGaussian_block_wick 4 id id i j

private theorem centeredQuadratic_product_entries (A : Fin 4 → Matrix I I ℂ) :
    (∏ a, gaussianCenteredQuadraticPolynomial (A a)) =
      ∑ i : Fin 4 → I, ∑ j : Fin 4 → I,
        C (∏ a, A a (i a) (j a)) *
          ∏ a, gaussianCenteredCoordinatePolynomial (i a) (j a) := by
  simp_rw [gaussianCenteredQuadraticPolynomial_entries, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.prod_mul_distrib, ← map_prod]

private def quadraticDerangements : Finset (Equiv.Perm (Fin 4)) :=
  Finset.univ.filter (fun π => ∀ a, a ≠ π a)

private theorem centeredQuadratic_fourth_entries (A : Fin 4 → Matrix I I ℂ) :
    complexGaussianPolyExpectation (∏ a, gaussianCenteredQuadraticPolynomial (A a)) =
      ∑ π ∈ quadraticDerangements, ∑ i : Fin 4 → I,
        ∏ a, A a (i a) (i (π.symm a)) := by
  rw [centeredQuadratic_product_entries]
  simp only [complexGaussianPolyExpectation_sum, complexGaussianPolyExpectation_C_mul,
    centeredCoordinate_fourth_pairings, complexGaussianBlockPairingSum, id_eq, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ (α := Equiv.Perm (Fin 4)))]
  rw [quadraticDerangements, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hp : ∀ a, a ≠ π a
  · rw [ite_eq_left hp]
    apply Finset.sum_congr rfl
    intro i _
    have he (j : Fin 4 → I) :
        (∏ a, if a ≠ π a ∧ i a = j (π a) then (1 : ℂ) else 0) =
          ∏ a, if i a = j (π a) then (1 : ℂ) else 0 := by
      apply Finset.prod_congr rfl
      intro a _
      by_cases hij : i a = j (π a)
      · exact (ite_eq_left ⟨hp a, hij⟩).trans (ite_eq_left hij).symm
      · exact (ite_eq_right (fun h => hij h.2)).trans (ite_eq_right hij).symm
    simp_rw [he]
    exact matrix_wick_delta_contraction A π i
  · rw [ite_eq_right hp]
    push Not at hp
    obtain ⟨a, ha⟩ := hp
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hz : (∏ b : Fin 4, if b ≠ π b ∧ i b = j (π b) then (1 : ℂ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      exact ite_eq_right (fun h => h.1 ha)
    rw [hz, mul_zero]

private theorem sum_quadraticDerangements (f : Equiv.Perm (Fin 4) → ℂ) :
    (∑ π ∈ quadraticDerangements, f π) =
      f (Equiv.swap 0 1 * Equiv.swap 2 3) +
      f (Equiv.swap 0 2 * Equiv.swap 1 3) +
      f (Equiv.swap 0 3 * Equiv.swap 1 2) +
      f (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) +
      f (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 2) +
      f (Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3) +
      f (Equiv.swap 0 2 * Equiv.swap 2 3 * Equiv.swap 3 1) +
      f (Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 2) +
      f (Equiv.swap 0 3 * Equiv.swap 3 2 * Equiv.swap 2 1) := by
  have he : quadraticDerangements =
      {Equiv.swap 0 1 * Equiv.swap 2 3,
       Equiv.swap 0 2 * Equiv.swap 1 3,
       Equiv.swap 0 3 * Equiv.swap 1 2,
       Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3,
       Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 2,
       Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3,
       Equiv.swap 0 2 * Equiv.swap 2 3 * Equiv.swap 3 1,
       Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 2,
       Equiv.swap 0 3 * Equiv.swap 3 2 * Equiv.swap 2 1} := by decide
  rw [he]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  ring

private def fourArrowEquiv : (Fin 4 → I) ≃ I × I × I × I where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

omit [DecidableEq I] in
private theorem sum_finFour_function {R : Type*} [AddCommMonoid R]
    (f : (Fin 4 → I) → R) :
    (∑ i, f i) = ∑ a, ∑ b, ∑ c, ∑ d, f ![a,b,c,d] := by
  rw [← (fourArrowEquiv (I := I)).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

omit [DecidableEq I] in
private theorem trace_pair_contraction (A B C D : Matrix I I ℂ) :
    (∑ x, ∑ y, ∑ z, ∑ t, A x y * (B y x * (C z t * D t z))) =
      (A*B).trace * (C*D).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, mul_assoc]

omit [DecidableEq I] in
private theorem trace_cycle_contraction (A B C D : Matrix I I ℂ) :
    (∑ x, ∑ y, ∑ z, ∑ t, A x y * (B y z * (C z t * D t x))) =
      (A*B*C*D).trace := by
  rw [Matrix.mul_assoc A B C, Matrix.mul_assoc A (B*C) D, Matrix.mul_assoc B C D]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]

omit [DecidableEq I] in
private theorem sum_three_rotate (f : I → I → I → ℂ) :
    (∑ y, ∑ z, ∑ t, f y z t) = ∑ t, ∑ y, ∑ z, f y z t := by
  calc
    _ = ∑ y, ∑ t, ∑ z, f y z t := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- The nine Wick derangements give three pair partitions and six four-cycles. -/
theorem gaussianCenteredQuadraticPolynomial_fourth (A B : Matrix I I ℂ) :
    complexGaussianPolyExpectation
      (gaussianCenteredQuadraticPolynomial A ^ 2 * gaussianCenteredQuadraticPolynomial B ^ 2) =
      (A^2).trace * (B^2).trace + 2 * (A*B).trace^2 +
        2 * (A*B*A*B).trace + 4 * (A^2*B^2).trace := by
  have h1 := trace_pair_contraction A A B B
  have h2 : (∑ x, ∑ y, ∑ z, ∑ t, A x z * (A y t * (B z x * B t y))) =
      (A*B).trace^2 := by
    rw [pow_two, ← trace_pair_contraction A B A B]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h3 : (∑ x, ∑ y, ∑ z, ∑ t, A x t * (A y z * (B z y * B t x))) =
      (A*B).trace^2 := by
    rw [pow_two, ← trace_pair_contraction A B A B]
    apply Finset.sum_congr rfl
    intro x _
    rw [sum_three_rotate]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h4 : (∑ x, ∑ y, ∑ z, ∑ t, A x t * (A y x * (B z y * B t z))) =
      (A*A*B*B).trace := by
    rw [← trace_cycle_contraction A A B B, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h5 : (∑ x, ∑ y, ∑ z, ∑ t, A x z * (A y x * (B z t * B t y))) =
      (A*A*B*B).trace := by
    rw [← trace_cycle_contraction A A B B, Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h6 : (∑ x, ∑ y, ∑ z, ∑ t, A x t * (A y z * (B z x * B t y))) =
      (A*B*A*B).trace := by
    rw [← trace_cycle_contraction A B A B]
    apply Finset.sum_congr rfl
    intro x _
    rw [sum_three_rotate]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h7 : (∑ x, ∑ y, ∑ z, ∑ t, A x y * (A y t * (B z x * B t z))) =
      (A*A*B*B).trace := by
    rw [← trace_cycle_contraction A A B B]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h8 : (∑ x, ∑ y, ∑ z, ∑ t, A x z * (A y t * (B z y * B t x))) =
      (A*B*A*B).trace := by
    rw [← trace_cycle_contraction A B A B]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h9 := trace_cycle_contraction A A B B
  have he : gaussianCenteredQuadraticPolynomial A ^ 2 * gaussianCenteredQuadraticPolynomial B ^ 2 =
      ∏ a : Fin 4, gaussianCenteredQuadraticPolynomial (![A,A,B,B] a) := by
    simp [Fin.prod_univ_succ, pow_two, mul_assoc]
  rw [he, centeredQuadratic_fourth_entries, sum_quadraticDerangements]
  simp only [sum_finFour_function]
  norm_num [Fin.prod_univ_succ, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.swap_apply_def]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp only [pow_two, Matrix.mul_assoc]
  ring

/-- The centered quadratic form, evaluated at the genuine standard complex Gaussian. -/
def complexGaussianCenteredQuadratic (A : Matrix I I ℂ) (x : Fin 2 × I → ℝ) : ℂ :=
  sphereQuadraticForm A (WithLp.toLp 2 (complexCoordinate x)) - A.trace

omit [DecidableEq I] in
theorem complexGaussianCenteredQuadratic_eq_polynomial (A : Matrix I I ℂ) :
    complexGaussianCenteredQuadratic A =
      complexCoordinatePolyEval (gaussianCenteredQuadraticPolynomial A) := by
  funext x
  exact (gaussianCenteredQuadraticPolynomial_eval A x).symm

omit [DecidableEq I] in
/-- Every finite Gaussian moment exists before any integral identity is used. -/
theorem complexGaussianCenteredQuadratic_memLp (A : Matrix I I ℂ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (complexGaussianCenteredQuadratic A) p (pairedGaussian I) := by
  rw [complexGaussianCenteredQuadratic_eq_polynomial]
  exact complexCoordinatePolyEval_memLp _ p hp

omit [DecidableEq I] in
theorem complexGaussianCenteredQuadratic_fourth_integrable (A B : Matrix I I ℂ) :
    Integrable (fun x => complexGaussianCenteredQuadratic A x ^ 2 *
      complexGaussianCenteredQuadratic B x ^ 2) (pairedGaussian I) := by
  have he : (fun x => complexGaussianCenteredQuadratic A x ^ 2 *
      complexGaussianCenteredQuadratic B x ^ 2) = complexCoordinatePolyEval
        (gaussianCenteredQuadraticPolynomial A ^ 2 * gaussianCenteredQuadraticPolynomial B ^ 2) := by
    funext x
    simp only [complexGaussianCenteredQuadratic_eq_polynomial, complexCoordinatePolyEval,
      map_mul, map_pow]
  rw [he]
  exact complexCoordinatePolyEval_integrable _

/-- The actual fourth centered quadratic moment for arbitrary, possibly noncommuting matrices. -/
theorem complexGaussian_centered_quadratic_fourth (A B : Matrix I I ℂ) :
    (∫ x,
      (sphereQuadraticForm A (WithLp.toLp 2 (complexCoordinate x)) - A.trace)^2 *
      (sphereQuadraticForm B (WithLp.toLp 2 (complexCoordinate x)) - B.trace)^2
      ∂pairedGaussian I) =
        (A^2).trace * (B^2).trace + 2 * (A*B).trace^2 +
        2 * (A*B*A*B).trace + 4 * (A^2*B^2).trace := by
  have h := gaussianCenteredQuadraticPolynomial_fourth A B
  simpa only [complexGaussianPolyExpectation, complexCoordinatePolyEval, map_mul, map_pow,
    show ∀ M : Matrix I I ℂ, ∀ x : Fin 2 × I → ℝ,
      eval (fun c => (x c : ℂ)) (gaussianCenteredQuadraticPolynomial M) =
        sphereQuadraticForm M (WithLp.toLp 2 (complexCoordinate x)) - M.trace from
        fun M x => gaussianCenteredQuadraticPolynomial_eval M x] using h

private theorem gaussianMatrixQuadraticPolynomial_mean (A : Matrix I I ℂ) :
    complexGaussianPolyExpectation (gaussianMatrixQuadraticPolynomial A) = A.trace := by
  have hcoord (i j : I) :
      complexGaussianPolyExpectation (gaussianBarZPolynomial i * gaussianZPolynomial j) =
        if i = j then 1 else 0 := by
    rw [complexGaussianPolyExpectation_barz_ibp, wirtingerZ_z]
    by_cases h : i = j <;>
      simp [h, complexGaussianPolyExpectation_one, complexGaussianPolyExpectation_zero]
  simp only [gaussianMatrixQuadraticPolynomial, mul_assoc,
    complexGaussianPolyExpectation_sum, complexGaussianPolyExpectation_C_mul, hcoord,
    mul_ite, mul_one, mul_zero]
  simp [Matrix.trace, Matrix.diag]

theorem gaussianCenteredQuadraticPolynomial_mean_zero (A : Matrix I I ℂ) :
    complexGaussianPolyExpectation (gaussianCenteredQuadraticPolynomial A) = 0 := by
  simp only [gaussianCenteredQuadraticPolynomial, complexGaussianPolyExpectation_sub,
    gaussianMatrixQuadraticPolynomial_mean, complexGaussianPolyExpectation_C, sub_self]

/-- The bilinear second moment has no conjugation and needs no Hermiticity hypothesis. -/
theorem gaussianCenteredQuadraticPolynomial_second (A B : Matrix I I ℂ) :
    complexGaussianPolyExpectation
      (gaussianCenteredQuadraticPolynomial A * gaussianCenteredQuadraticPolynomial B) =
        (A*B).trace := by
  have hn : complexGaussianPolyExpectation (gaussianNormalMatrixPolynomial A B) = 0 := by
    simp only [gaussianNormalMatrixPolynomial, complexGaussianPolyExpectation_sum,
      complexGaussianPolyExpectation_C_mul, gaussianNormalQuartic_mean_zero, mul_zero,
      Finset.sum_const_zero]
  rw [gaussianNormalMatrixPolynomial_expansion,
    ← gaussianCenteredQuadraticPolynomial, ← gaussianCenteredQuadraticPolynomial,
    complexGaussianPolyExpectation_add, complexGaussianPolyExpectation_sub,
    gaussianMatrixQuadraticPolynomial_mean, complexGaussianPolyExpectation_C,
    Matrix.trace_add, Matrix.trace_mul_comm B A] at hn
  linear_combination hn

theorem complexGaussian_centered_quadratic_second (A B : Matrix I I ℂ) :
    (∫ x, complexGaussianCenteredQuadratic A x * complexGaussianCenteredQuadratic B x
      ∂pairedGaussian I) = (A*B).trace := by
  have h := gaussianCenteredQuadraticPolynomial_second A B
  simpa only [complexGaussianPolyExpectation, complexGaussianCenteredQuadratic_eq_polynomial,
    complexCoordinatePolyEval, map_mul] using h

private theorem ofReal_re_of_star_eq (z : ℂ) (hz : star z = z) : (z.re : ℂ) = z := by
  have hi := congrArg Complex.im hz
  simp only [Complex.star_def, Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

omit [DecidableEq I] in
/-- Hermitian quadratic forms are real pointwise, without a positivity hypothesis. -/
theorem complexGaussianCenteredQuadratic_ofReal_re (A : Matrix I I ℂ)
    (hA : A.IsHermitian) (x : Fin 2 × I → ℝ) :
    ((complexGaussianCenteredQuadratic A x).re : ℂ) = complexGaussianCenteredQuadratic A x := by
  apply ofReal_re_of_star_eq
  simp only [complexGaussianCenteredQuadratic, star_sub, sphereQuadraticForm_star,
    ← Matrix.trace_conjTranspose, hA.eq]

omit [DecidableEq I] in
private theorem trace_mul_hermitian_ofReal_re (A B : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : ((A*B).trace.re : ℂ) = (A*B).trace := by
  apply ofReal_re_of_star_eq
  simp only [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq]
  exact Matrix.trace_mul_comm B A

omit [DecidableEq I] in
/-- The squared real Hermitian observable has a finite second moment. -/
theorem complexGaussianCenteredQuadratic_real_square_memLp (A : Matrix I I ℂ)
    (hA : A.IsHermitian) :
    MemLp (fun x => (complexGaussianCenteredQuadratic A x).re ^ 2) 2 (pairedGaussian I) := by
  have hpoly := complexCoordinatePolyEval_memLp (gaussianCenteredQuadraticPolynomial A ^ 2)
    2 (by norm_num)
  have heval (x : Fin 2 × I → ℝ) :
      complexCoordinatePolyEval (gaussianCenteredQuadraticPolynomial A ^ 2) x =
        complexGaussianCenteredQuadratic A x ^ 2 := by
    simp only [complexGaussianCenteredQuadratic_eq_polynomial, complexCoordinatePolyEval, map_pow]
  have he : (fun x => (complexGaussianCenteredQuadratic A x).re ^ 2) =
      fun x => (complexCoordinatePolyEval (gaussianCenteredQuadraticPolynomial A ^ 2) x).re := by
    funext x
    rw [heval, ← complexGaussianCenteredQuadratic_ofReal_re A hA x]
    simp [pow_two]
  rw [he]
  exact hpoly.re

theorem complexGaussian_centered_quadratic_real_second (A : Matrix I I ℂ)
    (hA : A.IsHermitian) :
    (∫ x, (complexGaussianCenteredQuadratic A x).re ^ 2 ∂pairedGaussian I) = (A^2).trace.re := by
  have h := complexGaussian_centered_quadratic_second A A
  have he : (fun x => complexGaussianCenteredQuadratic A x * complexGaussianCenteredQuadratic A x) =
      fun x => (((complexGaussianCenteredQuadratic A x).re ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [← complexGaussianCenteredQuadratic_ofReal_re A hA x]
    simp [pow_two]
  rw [he, integral_complex_ofReal] at h
  simpa only [Complex.ofReal_re, pow_two] using congrArg Complex.re h

theorem complexGaussian_centered_quadratic_real_fourth (A B : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∫ x, (complexGaussianCenteredQuadratic A x).re ^ 2 *
      (complexGaussianCenteredQuadratic B x).re ^ 2 ∂pairedGaussian I) =
        (A^2).trace.re * (B^2).trace.re + 2 * (A*B).trace.re ^ 2 +
          2 * (A*B*A*B).trace.re + 4 * (A^2*B^2).trace.re := by
  have h := complexGaussian_centered_quadratic_fourth A B
  change (∫ x, complexGaussianCenteredQuadratic A x ^ 2 *
    complexGaussianCenteredQuadratic B x ^ 2 ∂pairedGaussian I) = _ at h
  have he : (fun x => complexGaussianCenteredQuadratic A x ^ 2 * complexGaussianCenteredQuadratic B x ^ 2) =
      fun x => (((complexGaussianCenteredQuadratic A x).re ^ 2 *
        (complexGaussianCenteredQuadratic B x).re ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [← complexGaussianCenteredQuadratic_ofReal_re A hA x,
      ← complexGaussianCenteredQuadratic_ofReal_re B hB x]
    simp
  rw [he, integral_complex_ofReal, pow_two A, pow_two B,
    ← trace_mul_hermitian_ofReal_re A A hA hA,
    ← trace_mul_hermitian_ofReal_re B B hB hB,
    ← trace_mul_hermitian_ofReal_re A B hA hB] at h
  simpa [pow_two] using congrArg Complex.re h

/-- The covariance of squared centered Hermitian quadratic forms. -/
theorem complexGaussian_centered_quadratic_square_covariance (A B : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ProbabilityTheory.covariance
      (fun x => (complexGaussianCenteredQuadratic A x).re ^ 2)
      (fun x => (complexGaussianCenteredQuadratic B x).re ^ 2) (pairedGaussian I) =
        2 * (A*B).trace.re ^ 2 + 2 * (A*B*A*B).trace.re + 4 * (A^2*B^2).trace.re := by
  let : IsProbabilityMeasure (pairedGaussian I) := by
    unfold pairedGaussian
    infer_instance
  rw [ProbabilityTheory.covariance_eq_sub
    (complexGaussianCenteredQuadratic_real_square_memLp A hA)
    (complexGaussianCenteredQuadratic_real_square_memLp B hB)]
  simp only [Pi.mul_apply]
  rw [complexGaussian_centered_quadratic_real_fourth A B hA hB,
    complexGaussian_centered_quadratic_real_second A hA,
    complexGaussian_centered_quadratic_real_second B hB]
  ring

end CertificationGaussian
