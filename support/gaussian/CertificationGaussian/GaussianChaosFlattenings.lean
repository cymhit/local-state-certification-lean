import CertificationGaussian.RectangularGaussianExpectation

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I R C : Type*} [Fintype I] [Fintype R] [Fintype C]
  [DecidableEq I] [DecidableEq R] [DecidableEq C]

/-- The four actual matricizations of one rectangular coefficient tensor. -/
def chaosFlattening₁ (A : I → I → Matrix R C ℂ) : Matrix R (I × I × C) ℂ :=
  fun r a => A a.1 a.2.1 r a.2.2

def chaosFlattening₂ (A : I → I → Matrix R C ℂ) : Matrix (I × I × R) C ℂ :=
  fun a c => A a.1 a.2.1 a.2.2 c

def chaosFlattening₃ (A : I → I → Matrix R C ℂ) : Matrix (I × R) (I × C) ℂ :=
  fun a b => A a.1 b.1 a.2 b.2

def chaosFlattening₄ (A : I → I → Matrix R C ℂ) : Matrix (I × R) (I × C) ℂ :=
  fun a b => A b.1 a.1 a.2 b.2

def chaosRowCoefficient (A : I → I → Matrix R C ℂ) (i : I) : Matrix R (I × C) ℂ :=
  fun r b => A i b.1 r b.2

def chaosColumnCoefficient (A : I → I → Matrix R C ℂ) (i : I) : Matrix (I × R) C ℂ :=
  fun a c => A i a.1 a.2 c

/-- Horizontal and vertical blocks retain the entire conditional covariance. -/
def matrixBlockRow (B : I → Matrix R C ℂ) : Matrix R (I × C) ℂ :=
  fun r a => B a.1 r a.2

def matrixBlockColumn (B : I → Matrix R C ℂ) : Matrix (I × R) C ℂ :=
  fun a c => B a.1 a.2 c

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype R] in
theorem matrixBlockRow_mul_conjTranspose (B : I → Matrix R C ℂ) :
    matrixBlockRow B * (matrixBlockRow B)ᴴ = gaussianLeftCovariance B := by
  ext r s
  simp [matrixBlockRow, gaussianLeftCovariance, Matrix.mul_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype C] in
theorem matrixBlockColumn_conjTranspose_mul (B : I → Matrix R C ℂ) :
    (matrixBlockColumn B)ᴴ * matrixBlockColumn B = gaussianRightCovariance B := by
  ext c e
  simp [matrixBlockColumn, gaussianRightCovariance, Matrix.mul_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype R] in
theorem chaosRow_leftCovariance (A : I → I → Matrix R C ℂ) :
    gaussianLeftCovariance (chaosRowCoefficient A) = chaosFlattening₁ A * (chaosFlattening₁ A)ᴴ := by
  ext r s
  simp [gaussianLeftCovariance, chaosRowCoefficient, chaosFlattening₁, Matrix.mul_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype C] in
theorem chaosRow_rightCovariance (A : I → I → Matrix R C ℂ) :
    gaussianRightCovariance (chaosRowCoefficient A) = (chaosFlattening₃ A)ᴴ * chaosFlattening₃ A := by
  ext a b
  simp [gaussianRightCovariance, chaosRowCoefficient, chaosFlattening₃, Matrix.mul_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype R] in
theorem chaosColumn_leftCovariance (A : I → I → Matrix R C ℂ) :
    gaussianLeftCovariance (chaosColumnCoefficient A) = chaosFlattening₄ A * (chaosFlattening₄ A)ᴴ := by
  ext a b
  simp [gaussianLeftCovariance, chaosColumnCoefficient, chaosFlattening₄, Matrix.mul_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype C] in
theorem chaosColumn_rightCovariance (A : I → I → Matrix R C ℂ) :
    gaussianRightCovariance (chaosColumnCoefficient A) = (chaosFlattening₂ A)ᴴ * chaosFlattening₂ A := by
  ext c e
  simp [gaussianRightCovariance, chaosColumnCoefficient, chaosFlattening₂, Matrix.mul_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype R] [Fintype C] in
theorem gaussianMatrixSeries_blockRow (A : I → I → Matrix R C ℂ) (x : I → ℝ) :
    gaussianMatrixSeries (chaosRowCoefficient A) x =
      matrixBlockRow (fun j => gaussianMatrixSeries (fun i => A i j) x) := by
  ext r a
  simp [gaussianMatrixSeries, chaosRowCoefficient, matrixBlockRow, Matrix.sum_apply]

omit [DecidableEq I] [DecidableEq R] [DecidableEq C] [Fintype R] [Fintype C] in
theorem gaussianMatrixSeries_blockColumn (A : I → I → Matrix R C ℂ) (x : I → ℝ) :
    gaussianMatrixSeries (chaosColumnCoefficient A) x =
      matrixBlockColumn (fun j => gaussianMatrixSeries (fun i => A i j) x) := by
  ext a c
  simp [gaussianMatrixSeries, chaosColumnCoefficient, matrixBlockColumn, Matrix.sum_apply]

omit [Fintype I] [DecidableEq I] [DecidableEq R] in
theorem sqrt_rightGram_opNorm (B : Matrix R C ℂ) :
    Real.sqrt ‖Matrix.toEuclideanCLM (n := C) (𝕜 := ℂ) (Bᴴ * B)‖ =
      ‖rectangularEuclideanCLM B‖ := by
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_conjTranspose_mul_self,
    ← pow_two, Real.sqrt_sq (norm_nonneg B), rectangularEuclideanCLM_norm]

omit [Fintype I] [DecidableEq I] in
theorem sqrt_leftGram_opNorm (B : Matrix R C ℂ) :
    Real.sqrt ‖Matrix.toEuclideanCLM (n := R) (𝕜 := ℂ) (B * Bᴴ)‖ =
      ‖rectangularEuclideanCLM B‖ := by
  have h := sqrt_rightGram_opNorm Bᴴ
  simpa only [Matrix.conjTranspose_conjTranspose, rectangularEuclideanCLM_norm,
    Matrix.l2_opNorm_conjTranspose] using h

/-- The conditional first Gaussian estimate uses whole block operators. -/
theorem rectangularGaussian_expectation_bound_blocks (B : I → Matrix R C ℂ) :
    (∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries B x)‖ ∂realGaussianProduct I) ≤
      gaussianMatrixExpectationConstant * Real.sqrt (Real.log (2*((Fintype.card R:ℝ)+Fintype.card C))) *
        max ‖rectangularEuclideanCLM (matrixBlockRow B)‖
          ‖rectangularEuclideanCLM (matrixBlockColumn B)‖ := by
  have h := rectangularGaussian_expectation_bound B
  rw [← matrixBlockRow_mul_conjTranspose, ← matrixBlockColumn_conjTranspose_mul,
    sqrt_leftGram_opNorm, sqrt_rightGram_opNorm] at h
  exact h

/-- The row operator has the first and third flattenings as its two covariances. -/
theorem gaussianChaosRow_expectation_bound (A : I → I → Matrix R C ℂ) :
    (∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries (chaosRowCoefficient A) x)‖
      ∂realGaussianProduct I) ≤ gaussianMatrixExpectationConstant *
      Real.sqrt (Real.log (2*((Fintype.card R:ℝ)+(Fintype.card I:ℝ)*Fintype.card C))) *
        max ‖rectangularEuclideanCLM (chaosFlattening₁ A)‖
          ‖rectangularEuclideanCLM (chaosFlattening₃ A)‖ := by
  have h := rectangularGaussian_expectation_bound (chaosRowCoefficient A)
  rw [chaosRow_leftCovariance, chaosRow_rightCovariance,
    sqrt_leftGram_opNorm, sqrt_rightGram_opNorm] at h
  simpa only [Fintype.card_prod, Nat.cast_mul] using h

/-- The column operator has the fourth and second flattenings as its two covariances. -/
theorem gaussianChaosColumn_expectation_bound (A : I → I → Matrix R C ℂ) :
    (∫ x, ‖rectangularEuclideanCLM (gaussianMatrixSeries (chaosColumnCoefficient A) x)‖
      ∂realGaussianProduct I) ≤ gaussianMatrixExpectationConstant *
      Real.sqrt (Real.log (2*((Fintype.card I:ℝ)*Fintype.card R+Fintype.card C))) *
        max ‖rectangularEuclideanCLM (chaosFlattening₄ A)‖
          ‖rectangularEuclideanCLM (chaosFlattening₂ A)‖ := by
  have h := rectangularGaussian_expectation_bound (chaosColumnCoefficient A)
  rw [chaosColumn_leftCovariance, chaosColumn_rightCovariance,
    sqrt_leftGram_opNorm, sqrt_rightGram_opNorm] at h
  simpa only [Fintype.card_prod, Nat.cast_mul] using h

end CertificationGaussian
