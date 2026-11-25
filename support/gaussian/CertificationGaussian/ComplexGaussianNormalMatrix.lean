import CertificationGaussian.ComplexGaussianNormalOrder
import CertificationGaussian.SphereQuadraticMoments

noncomputable section
open MeasureTheory MvPolynomial Finset Matrix
open scoped BigOperators ENNReal
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual z-adjoint A z as a polynomial in the original real Gaussian coordinates. -/
def gaussianMatrixQuadraticPolynomial (A : Matrix I I ℂ) : MvPolynomial (Fin 2 × I) ℂ :=
  ∑ a, ∑ c, C (A a c) * gaussianBarZPolynomial a * gaussianZPolynomial c

/-- Finite matrix-entry contraction of the genuine seven-term normal blocks. -/
def gaussianNormalMatrixPolynomial (A B : Matrix I I ℂ) : MvPolynomial (Fin 2 × I) ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, C (A a c * B b d) * gaussianNormalQuartic a b c d

/-- The normal-ordered quadratic product W_z(A,B) for arbitrary complex matrices. -/
def complexGaussianNormalMatrix (A B : Matrix I I ℂ) (z : I → ℂ) : ℂ :=
  (sphereQuadraticForm A (WithLp.toLp 2 z)-Matrix.trace A) *
    (sphereQuadraticForm B (WithLp.toLp 2 z)-Matrix.trace B) -
    sphereQuadraticForm (A*B+B*A) (WithLp.toLp 2 z) + Matrix.trace (A*B)

omit [DecidableEq I] in
theorem gaussianMatrixQuadraticPolynomial_eval (A : Matrix I I ℂ) (x : Fin 2 × I → ℝ) :
    complexCoordinatePolyEval (gaussianMatrixQuadraticPolynomial A) x =
      sphereQuadraticForm A (WithLp.toLp 2 (complexCoordinate x)) := by
  simp only [gaussianMatrixQuadraticPolynomial, complexCoordinatePolyEval, map_sum,
    map_mul, eval_C, sphereQuadraticForm,
    show ∀ k, eval (fun c => (x c:ℂ)) (gaussianZPolynomial k) = complexCoordinate x k from
      fun k => complexCoordinatePolyEval_z k x,
    show ∀ k, eval (fun c => (x c:ℂ)) (gaussianBarZPolynomial k) = star (complexCoordinate x k) from
      fun k => complexCoordinatePolyEval_barz k x]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Finite contraction gives the normal-order correction with both products AB and BA. -/
theorem gaussianNormalMatrixPolynomial_expansion (A B : Matrix I I ℂ) :
    gaussianNormalMatrixPolynomial A B =
      (gaussianMatrixQuadraticPolynomial A-C (Matrix.trace A)) *
        (gaussianMatrixQuadraticPolynomial B-C (Matrix.trace B)) -
        gaussianMatrixQuadraticPolynomial (A*B+B*A) + C (Matrix.trace (A*B)) := by
  let u := gaussianBarZPolynomial (I := I)
  let v := gaussianZPolynomial (I := I)
  have h0 : (∑ a, ∑ b, ∑ c, ∑ d, C (A a c*B b d)*u a*u b*v c*v d) =
      gaussianMatrixQuadraticPolynomial A * gaussianMatrixQuadraticPolynomial B := by
    rw [mul_comm (gaussianMatrixQuadraticPolynomial A)]
    unfold gaussianMatrixQuadraticPolynomial
    simp only [Finset.sum_mul, Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    dsimp [u,v]
    ring
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d,
      C (A a c*B b d)*gaussianDeltaPolynomial a c*u b*v d) =
      C (Matrix.trace A)*gaussianMatrixQuadraticPolynomial B := by
    simp [gaussianDeltaPolynomial, apply_ite, ite_mul, Matrix.trace, Matrix.diag,
      gaussianMatrixQuadraticPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
      u,v, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  have h2 : (∑ a, ∑ b, ∑ c, ∑ d,
      C (A a c*B b d)*gaussianDeltaPolynomial a d*u b*v c) =
      gaussianMatrixQuadraticPolynomial (B*A) := by
    simp [gaussianDeltaPolynomial, apply_ite, ite_mul,
      gaussianMatrixQuadraticPolynomial, Matrix.mul_apply, map_sum, map_mul,
      Finset.sum_mul, u,v, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h3 : (∑ a, ∑ b, ∑ c, ∑ d,
      C (A a c*B b d)*gaussianDeltaPolynomial b c*u a*v d) =
      gaussianMatrixQuadraticPolynomial (A*B) := by
    simp [gaussianDeltaPolynomial, apply_ite, ite_mul,
      gaussianMatrixQuadraticPolynomial, Matrix.mul_apply, map_sum, map_mul,
      Finset.sum_mul, u,v, mul_assoc]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have h4 : (∑ a, ∑ b, ∑ c, ∑ d,
      C (A a c*B b d)*gaussianDeltaPolynomial b d*u a*v c) =
      C (Matrix.trace B)*gaussianMatrixQuadraticPolynomial A := by
    simp [gaussianDeltaPolynomial, apply_ite, ite_mul, Matrix.trace, Matrix.diag,
      gaussianMatrixQuadraticPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
      u,v, mul_assoc]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have h5 : (∑ a, ∑ b, ∑ c, ∑ d,
      C (A a c*B b d)*gaussianDeltaPolynomial a c*gaussianDeltaPolynomial b d) =
      C (Matrix.trace A)*C (Matrix.trace B) := by
    simp [gaussianDeltaPolynomial, apply_ite, Matrix.trace, Matrix.diag,
      map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have h6 : (∑ a, ∑ b, ∑ c, ∑ d,
      C (A a c*B b d)*gaussianDeltaPolynomial a d*gaussianDeltaPolynomial b c) =
      C (Matrix.trace (A*B)) := by
    simp [gaussianDeltaPolynomial, apply_ite, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, map_sum, map_mul]
  have hadd : gaussianMatrixQuadraticPolynomial (A*B+B*A) =
      gaussianMatrixQuadraticPolynomial (A*B)+gaussianMatrixQuadraticPolynomial (B*A) := by
    simp [gaussianMatrixQuadraticPolynomial, map_add, add_mul, Finset.sum_add_distrib]
  unfold gaussianNormalMatrixPolynomial
  simp_rw [gaussianNormalQuartic_expansion]
  simp only [mul_add, mul_sub, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  change _ = _
  rw [h0,h1,h2,h3,h4,h5,h6,hadd]
  ring

/-- Evaluation of the contracted polynomial gives the normal-ordered product. -/
theorem gaussianNormalMatrixPolynomial_eval (A B : Matrix I I ℂ) (x : Fin 2 × I → ℝ) :
    complexCoordinatePolyEval (gaussianNormalMatrixPolynomial A B) x =
      complexGaussianNormalMatrix A B (complexCoordinate x) := by
  rw [gaussianNormalMatrixPolynomial_expansion]
  simp only [complexCoordinatePolyEval, map_add, map_sub, map_mul, eval_C,
    show ∀ M : Matrix I I ℂ, eval (fun c => (x c:ℂ)) (gaussianMatrixQuadraticPolynomial M) =
      sphereQuadraticForm M (WithLp.toLp 2 (complexCoordinate x)) from
      fun M => gaussianMatrixQuadraticPolynomial_eval M x]
  rfl

/-- All finite Gaussian Lp norms of this actual quartic are finite. -/
theorem complexGaussianNormalMatrix_memLp (A B : Matrix I I ℂ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => complexGaussianNormalMatrix A B (complexCoordinate x)) p (pairedGaussian I) := by
  have he : (fun x => complexGaussianNormalMatrix A B (complexCoordinate x)) =
      complexCoordinatePolyEval (gaussianNormalMatrixPolynomial A B) :=
    funext (fun x => (gaussianNormalMatrixPolynomial_eval A B x).symm)
  rw [he]
  exact complexCoordinatePolyEval_memLp _ p hp

theorem complexGaussianNormalMatrix_integrable (A B : Matrix I I ℂ) :
    Integrable (fun x => complexGaussianNormalMatrix A B (complexCoordinate x)) (pairedGaussian I) := by
  have he : (fun x => complexGaussianNormalMatrix A B (complexCoordinate x)) =
      complexCoordinatePolyEval (gaussianNormalMatrixPolynomial A B) :=
    funext (fun x => (gaussianNormalMatrixPolynomial_eval A B x).symm)
  rw [he]
  exact complexCoordinatePolyEval_integrable _

/-- Mean zero follows from the actual creation/derivative identity, for arbitrary complex A and B. -/
theorem complexGaussianNormalMatrix_mean_zero (A B : Matrix I I ℂ) :
    (∫ x, complexGaussianNormalMatrix A B (complexCoordinate x) ∂pairedGaussian I) = 0 := by
  have he : (fun x => complexGaussianNormalMatrix A B (complexCoordinate x)) =
      complexCoordinatePolyEval (gaussianNormalMatrixPolynomial A B) :=
    funext (fun x => (gaussianNormalMatrixPolynomial_eval A B x).symm)
  rw [he]
  change complexGaussianPolyExpectation (gaussianNormalMatrixPolynomial A B)=0
  simp only [gaussianNormalMatrixPolynomial, complexGaussianPolyExpectation_sum,
    complexGaussianPolyExpectation_C_mul, gaussianNormalQuartic_mean_zero, mul_zero,
    Finset.sum_const_zero]

omit [DecidableEq I] in
/-- Conjugation of the true quadratic form is the adjoint matrix quadratic form. -/
theorem sphereQuadraticForm_star (A : Matrix I I ℂ) (z : EuclideanSpace ℂ I) :
    star (sphereQuadraticForm A z) = sphereQuadraticForm Aᴴ z := by
  simp only [sphereQuadraticForm, star_sum, star_mul, star_star, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [DecidableEq I] in
/-- The normal-ordered product of Hermitian inputs is real. -/
theorem complexGaussianNormalMatrix_star_of_hermitian (A B : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (z : I → ℂ) :
    star (complexGaussianNormalMatrix A B z) = complexGaussianNormalMatrix A B z := by
  simp only [complexGaussianNormalMatrix, star_add, star_sub, star_mul,
    sphereQuadraticForm_star, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hA.eq, hB.eq]
  rw [add_comm (B*A), Matrix.trace_mul_comm B A]
  ring

end CertificationGaussian
