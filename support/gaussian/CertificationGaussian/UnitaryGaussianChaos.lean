import CertificationGaussian.UnitaryBellFlattenings

noncomputable section
open Matrix Finset MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

omit [Fintype K] [DecidableEq K] [DecidableEq I] in
theorem chaosFlattening₁_gram (A : I → I → Matrix I I ℂ) :
    chaosFlattening₁ A * (chaosFlattening₁ A)ᴴ = ∑ i, ∑ j, A i j * (A i j)ᴴ := by
  ext r s
  simp [chaosFlattening₁, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

omit [Fintype K] [DecidableEq K] [DecidableEq I] in
theorem chaosFlattening₂_gram (A : I → I → Matrix I I ℂ) :
    (chaosFlattening₂ A)ᴴ * chaosFlattening₂ A = ∑ i, ∑ j, (A i j)ᴴ * A i j := by
  ext r s
  simp [chaosFlattening₂, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

/-- The common row/column covariance scale, before taking the square root. -/
def unitaryWeightSquareMean (a : K → ℝ) : ℝ := (∑ w, (a w)^2)/(Fintype.card I:ℝ)

omit [DecidableEq I] [DecidableEq K] in
theorem unitaryWeightSquareMean_nonneg (a : K → ℝ) : 0 ≤ unitaryWeightSquareMean (I := I) a :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

omit [DecidableEq K] in
theorem unitary_scalar_covariance_norm [Nonempty I] (a : K → ℝ) :
    ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
      (((∑ w, (a w:ℂ)^2)/(Fintype.card I:ℂ)) • (1 : Matrix I I ℂ))‖ =
      unitaryWeightSquareMean (I := I) a := by
  have hc : ((∑ w, (a w:ℂ)^2)/(Fintype.card I:ℂ)) =
      (unitaryWeightSquareMean (I := I) a : ℂ) := by
    simp [unitaryWeightSquareMean]
  rw [hc, Matrix.l2_opNorm_toEuclideanCLM, norm_smul, norm_one, mul_one]
  exact Complex.norm_of_nonneg (unitaryWeightSquareMean_nonneg a)

theorem chaosFlattening₁_unitary_norm [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    ‖rectangularEuclideanCLM (chaosFlattening₁ (unitaryChaosCoefficient W a))‖ =
      Real.sqrt (unitaryWeightSquareMean (I := I) a) := by
  rw [← sqrt_leftGram_opNorm, chaosFlattening₁_gram,
    unitaryChaosCoefficient_leftGram W a hW hHS, unitary_scalar_covariance_norm]

theorem chaosFlattening₂_unitary_norm [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    ‖rectangularEuclideanCLM (chaosFlattening₂ (unitaryChaosCoefficient W a))‖ =
      Real.sqrt (unitaryWeightSquareMean (I := I) a) := by
  rw [← sqrt_rightGram_opNorm, chaosFlattening₂_gram,
    unitaryChaosCoefficient_rightGram W a hW hHS, unitary_scalar_covariance_norm]

/-- The genuine weighted conjugates of a rank-one matrix, with the paper's factor 1/D. -/
def unitaryWeightedRankOne (W : K → Matrix I I ℂ) (a : K → ℝ) (z : I → ℂ) : Matrix I I ℂ :=
  (Fintype.card I:ℂ)⁻¹ • ∑ w, (a w:ℂ) •
    (W w * Matrix.vecMulVec z (fun j => star (z j)) * (W w)ᴴ)

omit [DecidableEq K] in
theorem matrixSesquilinear_unitaryChaosCoefficient (W : K → Matrix I I ℂ) (a : K → ℝ)
    (z : I → ℂ) :
    matrixSesquilinear (unitaryChaosCoefficient W a) z z = unitaryWeightedRankOne W a z := by
  have hE (U : Matrix I I ℂ) :
      (∑ i, ∑ j, (z i * star (z j)) • (U * Matrix.single i j (1:ℂ) * Uᴴ)) =
        U * Matrix.vecMulVec z (fun j => star (z j)) * Uᴴ := by
    ext r s
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.single, ite_and]
    ring
  have hswitch (f : I → I → K → Matrix I I ℂ) :
      (∑ i, ∑ j, ∑ w, f i j w) = ∑ w, ∑ i, ∑ j, f i j w := by
    calc
      _ = ∑ i, ∑ w, ∑ j, f i j w := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  calc
    matrixSesquilinear (unitaryChaosCoefficient W a) z z =
        (Fintype.card I:ℂ)⁻¹ • ∑ i, ∑ j, ∑ w,
          (a w:ℂ) • ((z i * star (z j)) • (W w * Matrix.single i j (1:ℂ) * (W w)ᴴ)) := by
      simp only [matrixSesquilinear, unitaryChaosCoefficient, Finset.smul_sum, smul_smul]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = (Fintype.card I:ℂ)⁻¹ • ∑ w, (a w:ℂ) •
        ∑ i, ∑ j, (z i * star (z j)) • (W w * Matrix.single i j (1:ℂ) * (W w)ᴴ) := by
      rw [hswitch]
      simp only [Finset.smul_sum]
    _ = unitaryWeightedRankOne W a z := by simp only [hE, unitaryWeightedRankOne]


/-- All four flattenings reduce to exactly the paper's three controls. -/
theorem unitaryChaosCoefficient_flatteningNorm [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    gaussianChaosFlatteningNorm (unitaryChaosCoefficient W a) =
      max (Real.sqrt (unitaryWeightSquareMean (I := I) a))
        (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix W a))‖) := by
  simp only [gaussianChaosFlatteningNorm, chaosFlattening₁_unitary_norm W a hW hHS,
    chaosFlattening₂_unitary_norm W a hW hHS, max_self,
    chaosFlattening₃_unitaryChaosCoefficient, chaosFlattening₄_unitaryChaosCoefficient,
    weightedBellMatrix_norm W a hHS]

/-- The actual matrix-valued random variable K_a, driven by the already fixed CN(0,1) coordinates. -/
def unitaryGaussianConjugation (W : K → Matrix I I ℂ) (a : K → ℝ)
    (x : (Fin 2 × I) → ℝ) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  rectangularEuclideanCLM (unitaryWeightedRankOne W a (complexCoordinate x))

omit [DecidableEq K] in
theorem unitaryGaussianConjugation_eq_quadratic (W : K → Matrix I I ℂ) (a : K → ℝ)
    (x : (Fin 2 × I) → ℝ) :
    unitaryGaussianConjugation W a x = complexGaussianQuadratic (unitaryChaosCoefficient W a) x := by
  unfold unitaryGaussianConjugation complexGaussianQuadratic
  rw [matrixSesquilinear_unitaryChaosCoefficient]

omit [DecidableEq K] in
theorem unitaryGaussianConjugation_integrable (W : K → Matrix I I ℂ) (a : K → ℝ) :
    Integrable (unitaryGaussianConjugation W a) (pairedGaussian I) := by
  simpa only [show unitaryGaussianConjugation W a = complexGaussianQuadratic (unitaryChaosCoefficient W a)
    from funext (unitaryGaussianConjugation_eq_quadratic W a)] using
      complexGaussianQuadratic_integrable (unitaryChaosCoefficient W a)

omit [DecidableEq K] in
theorem unitaryGaussianConjugation_mean (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ)) :
    (∫ x, unitaryGaussianConjugation W a x ∂pairedGaussian I) =
      rectangularEuclideanCLM (((∑ w, (a w:ℂ))/(Fintype.card I:ℂ)) • (1 : Matrix I I ℂ)) := by
  simp_rw [unitaryGaussianConjugation_eq_quadratic]
  rw [complexGaussianQuadratic_integral, unitaryChaosCoefficient_diagonal_sum W a hW]

/-- Centered expectation for any finite unitary Hilbert-Schmidt orthogonal family, not necessarily a basis.
The constant is absolute; weights may be negative or zero. -/
theorem unitaryGaussianConjugation_expectation_bound [Nonempty I]
    (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    (∫ x, ‖unitaryGaussianConjugation W a x -
      rectangularEuclideanCLM (((∑ w, (a w:ℂ))/(Fintype.card I:ℂ)) • (1 : Matrix I I ℂ))‖
      ∂pairedGaussian I) ≤
        (8*gaussianMatrixChaosConstant) * Real.log (2*(Fintype.card I:ℝ)) *
          max (Real.sqrt (unitaryWeightSquareMean (I := I) a))
            (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix W a))‖) := by
  have h := complexGaussianQuadratic_equal_dimension_bound (unitaryChaosCoefficient W a)
  rw [unitaryChaosCoefficient_diagonal_sum W a hW,
    unitaryChaosCoefficient_flatteningNorm W a hW hHS] at h
  simpa only [unitaryGaussianConjugation_eq_quadratic] using h

end CertificationGaussian
