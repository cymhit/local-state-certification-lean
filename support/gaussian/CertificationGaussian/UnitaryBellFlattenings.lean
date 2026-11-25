import CertificationGaussian.UnitaryChaosCoefficients
import Mathlib.Analysis.InnerProductSpace.Orthonormal

noncomputable section
open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

/-- Vectorization in the paper's order: the first index labels the original basis vector. -/
def unitaryBellVector (U : Matrix I I ℂ) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (fun p => U p.2 p.1/(Real.sqrt (Fintype.card I:ℝ):ℂ))

omit [Fintype K] [DecidableEq K] [DecidableEq I] in
theorem unitaryBellVector_inner (U V : Matrix I I ℂ) :
    inner ℂ (unitaryBellVector U) (unitaryBellVector V) =
      Matrix.trace (Uᴴ*V)/(Fintype.card I:ℂ) := by
  have hs : (Real.sqrt (Fintype.card I:ℝ):ℂ)^2 = (Fintype.card I:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I))
  have ht (i j : I) : star (U j i/(Real.sqrt (Fintype.card I:ℝ):ℂ)) *
      (V j i/(Real.sqrt (Fintype.card I:ℝ):ℂ)) =
      (star (U j i)*V j i)/(Fintype.card I:ℂ) := by
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, ← pow_two, hs]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ p : I × I, (V p.2 p.1/(Real.sqrt (Fintype.card I:ℝ):ℂ)) *
    star (U p.2 p.1/(Real.sqrt (Fintype.card I:ℝ):ℂ))) = _
  simp_rw [mul_comm (V _ _ / _)]
  rw [Fintype.sum_prod_type]
  simp_rw [ht]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_div]

omit [Fintype K] [DecidableEq I] in
/-- Hilbert-Schmidt orthogonality becomes actual Bell-vector orthonormality. -/
theorem unitaryBellVector_orthonormal [Nonempty I] (W : K → Matrix I I ℂ)
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    Orthonormal ℂ (fun w => unitaryBellVector (W w)) := by
  have hD : (Fintype.card I:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [orthonormal_iff_ite]
  intro w v
  rw [unitaryBellVector_inner, hHS]
  split_ifs <;> simp [hD]

/-- The actual real-weighted sum of Bell rank-one matrices. -/
def weightedBellMatrix (W : K → Matrix I I ℂ) (a : K → ℝ) : Matrix (I × I) (I × I) ℂ :=
  ∑ w, (a w:ℂ) • Matrix.vecMulVec (fun p => unitaryBellVector (W w) p)
    (fun p => star (unitaryBellVector (W w) p))

/-- Partial transposition on the first tensor factor, without conjugating either factor. -/
def partialTransposeFirst (M : Matrix (I × I) (I × I) ℂ) : Matrix (I × I) (I × I) ℂ :=
  fun p q => M (q.1,p.2) (p.1,q.2)

omit [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] in
theorem partialTransposeFirst_involutive (M : Matrix (I × I) (I × I) ℂ) :
    partialTransposeFirst (partialTransposeFirst M) = M := by
  ext ⟨i,r⟩ ⟨j,s⟩
  rfl


omit [DecidableEq K] in
theorem chaosFlattening₃_unitaryChaosCoefficient (W : K → Matrix I I ℂ) (a : K → ℝ) :
    chaosFlattening₃ (unitaryChaosCoefficient W a) = weightedBellMatrix W a := by
  have hs : (Real.sqrt (Fintype.card I:ℝ):ℂ)^2 = (Fintype.card I:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I))
  ext ⟨i,r⟩ ⟨j,s⟩
  simp only [chaosFlattening₃, unitaryChaosCoefficient_apply, weightedBellMatrix,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    unitaryBellVector, star_div₀, Complex.star_def, Complex.conj_ofReal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [div_mul_div_comm, ← pow_two, hs]
  ring

omit [DecidableEq K] in
theorem chaosFlattening₄_unitaryChaosCoefficient (W : K → Matrix I I ℂ) (a : K → ℝ) :
    chaosFlattening₄ (unitaryChaosCoefficient W a) = partialTransposeFirst (weightedBellMatrix W a) := by
  rw [← chaosFlattening₃_unitaryChaosCoefficient]
  rfl


omit [DecidableEq I] [DecidableEq K] in
theorem bell_orthonormal_sum_norm_sq (v : K → EuclideanSpace ℂ (I × I))
    (hv : Orthonormal ℂ v) (c : K → ℂ) :
    ‖∑ w, c w • v w‖^2 = ∑ w, ‖c w‖^2 := by
  have h := congrArg Complex.re (hv.inner_sum c c Finset.univ)
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro w _
  rw [Complex.sq_norm, Complex.normSq_apply]

omit [DecidableEq K] in
theorem weightedBellMatrix_apply (W : K → Matrix I I ℂ) (a : K → ℝ)
    (x : EuclideanSpace ℂ (I × I)) :
    rectangularEuclideanCLM (weightedBellMatrix W a) x =
      ∑ w, ((a w:ℂ) * inner ℂ (unitaryBellVector (W w)) x) • unitaryBellVector (W w) := by
  ext p
  change (weightedBellMatrix W a *ᵥ WithLp.ofLp x) p = _
  simp only [weightedBellMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ w, (a w:ℂ) * ((unitaryBellVector (W w) p) *
    ((fun q => star (unitaryBellVector (W w) q)) ⬝ᵥ WithLp.ofLp x))) = _
  apply Finset.sum_congr rfl
  intro w _
  simp only [dotProduct_comm]
  change (a w:ℂ) * (unitaryBellVector (W w) p * (WithLp.ofLp x ⬝ᵥ star (WithLp.ofLp (unitaryBellVector (W w))))) =
    ((a w:ℂ) * (WithLp.ofLp x ⬝ᵥ star (WithLp.ofLp (unitaryBellVector (W w))))) * unitaryBellVector (W w) p
  ring

/-- A finite orthonormal Bell family suffices; no completeness of the unitary family is required. -/
theorem weightedBellMatrix_norm_le [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    ‖rectangularEuclideanCLM (weightedBellMatrix W a)‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hv := unitaryBellVector_orthonormal W hHS
  have hb := hv.sum_inner_products_le (s := Finset.univ) x
  have hsq : ‖rectangularEuclideanCLM (weightedBellMatrix W a) x‖^2 ≤ ‖a‖^2 * ‖x‖^2 := by
    rw [weightedBellMatrix_apply, bell_orthonormal_sum_norm_sq _ hv]
    calc
      ∑ w, ‖(a w:ℂ) * inner ℂ (unitaryBellVector (W w)) x‖^2
        ≤ ∑ w, ‖a‖^2 * ‖inner ℂ (unitaryBellVector (W w)) x‖^2 := by
          apply Finset.sum_le_sum
          intro w _
          rw [norm_mul, mul_pow, Complex.norm_real]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm a w) 2) (sq_nonneg _)
      _ = ‖a‖^2 * ∑ w, ‖inner ℂ (unitaryBellVector (W w)) x‖^2 := (Finset.mul_sum _ _ _).symm
      _ ≤ ‖a‖^2 * ‖x‖^2 := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
  nlinarith [norm_nonneg (rectangularEuclideanCLM (weightedBellMatrix W a) x), mul_nonneg (norm_nonneg a) (norm_nonneg x)]


theorem weightedBellMatrix_eigenvector [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) (w : K) :
    rectangularEuclideanCLM (weightedBellMatrix W a) (unitaryBellVector (W w)) =
      (a w:ℂ) • unitaryBellVector (W w) := by
  rw [weightedBellMatrix_apply]
  simp only [orthonormal_iff_ite.mp (unitaryBellVector_orthonormal W hHS), mul_ite,
    mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Exact maximum-weight norm, valid also for an empty family of Bell vectors. -/
theorem weightedBellMatrix_norm [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    ‖rectangularEuclideanCLM (weightedBellMatrix W a)‖ = ‖a‖ := by
  apply le_antisymm (weightedBellMatrix_norm_le W a hHS)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro w
  have h := (rectangularEuclideanCLM (weightedBellMatrix W a)).le_opNorm (unitaryBellVector (W w))
  rw [weightedBellMatrix_eigenvector W a hHS, norm_smul,
    (unitaryBellVector_orthonormal W hHS).norm_eq_one, Complex.norm_real, mul_one, mul_one] at h
  exact h

end CertificationGaussian
