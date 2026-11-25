import CertificationGaussian.UnitaryOrbitGram
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

noncomputable section
open Matrix Finset CFC
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace CertificationGaussian
variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- The actual functional-calculus inverse square root of the rectangular Gram matrix. -/
def matrixGramInverseSqrt (V : Matrix R C ℂ) : Matrix C C ℂ :=
  CFC.rpow (Vᴴ*V) (-(1/2:ℝ))

/-- The canonical polar correction V (V†V)^(-1/2). -/
def matrixPolarCorrection (V : Matrix R C ℂ) : Matrix R C ℂ := V * matrixGramInverseSqrt V

omit [DecidableEq R] in
theorem matrixGram_posDef_of_close (V : Matrix R C ℂ) (hV : ‖Vᴴ*V-1‖ < 1) :
    (Vᴴ*V).PosDef := by
  apply (Matrix.posSemidef_conjTranspose_mul_self V).posDef_iff_isUnit.mpr
  have h : ‖(1 : Matrix C C ℂ)-Vᴴ*V‖ < 1 := by rwa [norm_sub_rev]
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one h

omit [DecidableEq R] in
theorem matrixGramInverseSqrt_hermitian (V : Matrix R C ℂ) :
    (matrixGramInverseSqrt V).IsHermitian := by
  exact (CFC.rpow_nonneg (a := Vᴴ*V) (y := -(1/2:ℝ))).posSemidef.isHermitian

omit [DecidableEq R] in
/-- The actual correction has orthonormal columns whenever the Gram error is below one. -/
theorem matrixPolarCorrection_gram (V : Matrix R C ℂ) (hV : ‖Vᴴ*V-1‖ < 1) :
    (matrixPolarCorrection V)ᴴ * matrixPolarCorrection V = 1 := by
  have hS : (matrixGramInverseSqrt V)ᴴ = matrixGramInverseSqrt V :=
    (matrixGramInverseSqrt_hermitian V).eq
  calc
    _ = matrixGramInverseSqrt V * (Vᴴ*V) * matrixGramInverseSqrt V := by
      simp only [matrixPolarCorrection, Matrix.conjTranspose_mul, hS, Matrix.mul_assoc]
    _ = 1 := CFC.conjugate_rpow_neg_one_half (Vᴴ*V) (matrixGram_posDef_of_close V hV).isStrictlyPositive


/-- Scalar square-root contraction about the identity, including x=0. -/
theorem real_sqrt_sub_one_le (x : ℝ) (hx : 0 ≤ x) : |Real.sqrt x-1| ≤ |x-1| := by
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  rcases le_total (Real.sqrt x) 1 with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos (by nlinarith : x-1 ≤ 0)]
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (by nlinarith : 0 ≤ x-1)]
    nlinarith

omit [Fintype R] [DecidableEq R] in
/-- Functional calculus gives a genuine L2 operator-norm contraction about I for positive matrices. -/
theorem matrix_sqrt_sub_one_norm_le (G : Matrix C C ℂ) (hG : G.PosSemidef) :
    ‖CFC.sqrt G-1‖ ≤ ‖G-1‖ := by
  have hsqrt : cfc (fun x : ℝ => Real.sqrt x-1) G = CFC.sqrt G-1 := by
    erw [cfc_sub Real.sqrt (fun _ : ℝ => 1) G (by fun_prop) (by fun_prop),
      cfc_const_one ℝ G hG.isHermitian,
      CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hG.nonneg]
    simp only [Real.sqrt_eq_rpow]
  have hid : cfc (fun x : ℝ => x-1) G = G-1 := by
    erw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => 1) G (by fun_prop) (by fun_prop),
      cfc_id' ℝ G hG.isHermitian, cfc_const_one ℝ G hG.isHermitian]
  rw [← hsqrt]
  apply norm_cfc_le (norm_nonneg (G-1))
  intro x hx
  have h := norm_apply_le_norm_cfc (fun y : ℝ => y-1) G hx
    (by fun_prop) hG.isHermitian
  rw [hid] at h
  exact (real_sqrt_sub_one_le x (spectrum_nonneg_of_nonneg hG.nonneg hx)).trans h


omit [DecidableEq R] in
theorem matrixPolarCorrection_reconstruct (V : Matrix R C ℂ) (hV : ‖Vᴴ*V-1‖ < 1) :
    matrixPolarCorrection V * CFC.sqrt (Vᴴ*V) = V := by
  rw [matrixPolarCorrection, Matrix.mul_assoc, CFC.sqrt_eq_rpow]
  have h := CFC.rpow_neg_mul_rpow (a := Vᴴ*V) (1/2:ℝ)
    (matrixGram_posDef_of_close V hV).isStrictlyPositive
  change matrixGramInverseSqrt V * CFC.rpow (Vᴴ*V) (1/2:ℝ) = 1 at h
  erw [h, Matrix.mul_one]

omit [DecidableEq R] in
/-- Norm at most one, which also covers empty column spaces. -/
theorem matrixPolarCorrection_norm_le_one (V : Matrix R C ℂ) (hV : ‖Vᴴ*V-1‖ < 1) :
    ‖matrixPolarCorrection V‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (matrixPolarCorrection V)
  rw [matrixPolarCorrection_gram V hV] at h
  have h1 : ‖(1 : Matrix C C ℂ)‖ ≤ 1 := by
    cases isEmpty_or_nonempty C with
    | inl hC =>
      let := hC
      have hz : (1 : Matrix C C ℂ) = 0 := Subsingleton.elim _ _
      simp [hz]
    | inr hC =>
      let := hC
      simp
  nlinarith [norm_nonneg (matrixPolarCorrection V)]

omit [DecidableEq R] in
/-- The canonical inverse-square-root polar correction achieves the actual sharp Gram-error bound. -/
theorem matrixPolarCorrection_dist_le (V : Matrix R C ℂ) (hV : ‖Vᴴ*V-1‖ < 1) :
    ‖V-matrixPolarCorrection V‖ ≤ ‖Vᴴ*V-1‖ := by
  have he : V-matrixPolarCorrection V = matrixPolarCorrection V * (CFC.sqrt (Vᴴ*V)-1) := by
    rw [Matrix.mul_sub, matrixPolarCorrection_reconstruct V hV, Matrix.mul_one]
  rw [he]
  calc
    _ ≤ ‖matrixPolarCorrection V‖ * ‖CFC.sqrt (Vᴴ*V)-1‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ‖CFC.sqrt (Vᴴ*V)-1‖ := mul_le_mul_of_nonneg_right
      (matrixPolarCorrection_norm_le_one V hV) (norm_nonneg _)
    _ ≤ ‖Vᴴ*V-1‖ := by simpa only [one_mul] using
      matrix_sqrt_sub_one_norm_le (Vᴴ*V) (Matrix.posSemidef_conjTranspose_mul_self V)

omit [DecidableEq R] in
/-- Threshold form matching the actual orbit event, with arbitrary finite rectangular dimensions. -/
theorem matrixPolarCorrection_threshold (V : Matrix R C ℂ) {t : ℝ}
    (ht : t < 1) (hV : ‖Vᴴ*V-1‖ ≤ t) :
    (matrixPolarCorrection V)ᴴ * matrixPolarCorrection V = 1 ∧
      ‖V-matrixPolarCorrection V‖ ≤ t ∧ ‖matrixPolarCorrection V‖ ≤ 1 := by
  have hc := hV.trans_lt ht
  exact ⟨matrixPolarCorrection_gram V hc, (matrixPolarCorrection_dist_le V hc).trans hV,
    matrixPolarCorrection_norm_le_one V hc⟩


/-- The rectangular Euclidean operator has the expected genuine Hilbert-space adjoint. -/
theorem rectangularEuclideanCLM_adjoint (Q : Matrix R C ℂ) :
    ContinuousLinearMap.adjoint (rectangularEuclideanCLM Q) = rectangularEuclideanCLM Qᴴ := by
  simp only [rectangularEuclideanCLM, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_conjTranspose, LinearMap.adjoint_toContinuousLinearMap]

theorem rectangularGram_apply (Q : Matrix R C ℂ) (x : EuclideanSpace ℂ C) :
    rectangularEuclideanCLM Qᴴ (rectangularEuclideanCLM Q x) =
      Matrix.toEuclideanCLM (n := C) (𝕜 := ℂ) (Qᴴ*Q) x := by
  change WithLp.toLp 2 (Qᴴ *ᵥ (Q *ᵥ WithLp.ofLp x)) =
    WithLp.toLp 2 ((Qᴴ*Q) *ᵥ WithLp.ofLp x)
  rw [Matrix.mulVec_mulVec]

/-- A rectangular Gram identity provides actual norm preservation on all vectors. -/
theorem rectangularEuclideanCLM_norm_map_of_gram (Q : Matrix R C ℂ) (hQ : Qᴴ*Q=1)
    (x : EuclideanSpace ℂ C) : ‖rectangularEuclideanCLM Q x‖ = ‖x‖ := by
  have hi : inner ℂ (rectangularEuclideanCLM Q x) (rectangularEuclideanCLM Q x) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_right, rectangularEuclideanCLM_adjoint,
      rectangularGram_apply, hQ, map_one]
    rfl
  have hr := congrArg Complex.re hi
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] at hr
  nlinarith [norm_nonneg (rectangularEuclideanCLM Q x), norm_nonneg x]

/-- The same canonical Q, packaged as an actual linear isometry rather than an existence claim. -/
def matrixPolarLinearIsometry (V : Matrix R C ℂ) (hV : ‖Vᴴ*V-1‖ < 1) :
    EuclideanSpace ℂ C →ₗᵢ[ℂ] EuclideanSpace ℂ R where
  toLinearMap := (rectangularEuclideanCLM (matrixPolarCorrection V)).toLinearMap
  norm_map' := rectangularEuclideanCLM_norm_map_of_gram _ (matrixPolarCorrection_gram V hV)

theorem matrixPolarLinearIsometry_apply (V : Matrix R C ℂ) (hV : ‖Vᴴ*V-1‖ < 1)
    (x : EuclideanSpace ℂ C) :
    matrixPolarLinearIsometry V hV x = rectangularEuclideanCLM (matrixPolarCorrection V) x := rfl

/-- A deterministic conjugation perturbation inequality for arbitrary complex A. -/
theorem rectangular_conjugation_difference_le (V Q : Matrix R C ℂ) (A : Matrix C C ℂ) :
    ‖V*A*Vᴴ-Q*A*Qᴴ‖ ≤ ‖A‖*‖V-Q‖*(‖V‖+‖Q‖) := by
  have he : V*A*Vᴴ-Q*A*Qᴴ = (V-Q)*A*Vᴴ + Q*A*(Vᴴ-Qᴴ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(V-Q)*A*Vᴴ‖ + ‖Q*A*(Vᴴ-Qᴴ)‖ := norm_add_le _ _
    _ ≤ ‖V-Q‖*‖A‖*‖Vᴴ‖ + ‖Q‖*‖A‖*‖Vᴴ-Qᴴ‖ := by
      apply add_le_add
      · exact (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      · exact (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ = _ := by rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose,
      Matrix.l2_opNorm_conjTranspose]; ring

theorem matrixPolarCorrection_conjugation_le (V : Matrix R C ℂ) (A : Matrix C C ℂ)
    {t : ℝ} (ht : t<1) (hV : ‖Vᴴ*V-1‖ ≤ t) :
    ‖V*A*Vᴴ-matrixPolarCorrection V*A*(matrixPolarCorrection V)ᴴ‖ ≤ 3*‖A‖*t := by
  have ht0 : 0 ≤ t := (norm_nonneg _).trans hV
  have hc := hV.trans_lt ht
  have hQ := matrixPolarCorrection_norm_le_one V hc
  have hdist := (matrixPolarCorrection_dist_le V hc).trans hV
  have hVnorm : ‖V‖ ≤ 2 := by
    have he : V = (V-matrixPolarCorrection V)+matrixPolarCorrection V := by abel
    calc
      _ ≤ ‖V-matrixPolarCorrection V‖+‖matrixPolarCorrection V‖ := by
        conv_lhs => rw [he]
        exact norm_add_le _ _
      _ ≤ 2 := by linarith
  calc
    _ ≤ ‖A‖*‖V-matrixPolarCorrection V‖*(‖V‖+‖matrixPolarCorrection V‖) :=
      rectangular_conjugation_difference_le _ _ _
    _ ≤ ‖A‖*t*3 := mul_le_mul
      (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)) (by linarith)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) ht0)
    _ = _ := by ring

end CertificationGaussian
