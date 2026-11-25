import CertificationGaussian.ComplexGaussianQuadraticFrame

/-! # The actual local complement is a Hilbert–Schmidt contraction

We use complex Hilbert–Schmidt coordinates, then restrict scalars for the real
frame space. The map is defined on all matrices, not only diagonal matrices.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace CertificationGaussian

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def rankOneComplement (d : ℝ) (u : E) : E →L[ℂ] E :=
  (((d - 1)⁻¹ : ℝ) : ℂ) •
    (InnerProductSpace.rankOne ℂ u u - ContinuousLinearMap.id ℂ E)

theorem rankOneComplement_apply (d : ℝ) (u x : E) :
    rankOneComplement d u x = (((d - 1)⁻¹ : ℝ) : ℂ) • (inner ℂ u x • u - x) := rfl

theorem rankOneComplement_contraction (d : ℝ) (hd : 2 ≤ d) (u : E)
    (hu : ‖u‖^2 = d) (x : E) : ‖rankOneComplement d u x‖ ≤ ‖x‖ := by
  have hd1 : 0 < d - 1 := by linarith
  have hc : ‖inner ℂ u x‖^2 ≤ d * ‖x‖^2 := by
    calc
      _ ≤ (‖u‖ * ‖x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm u x) 2
      _ = _ := by rw [mul_pow, hu]
  have hi : (inner ℂ (inner ℂ u x • u) x).re = ‖inner ℂ u x‖^2 := by
    rw [inner_smul_left]
    simp only [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hs : ‖inner ℂ u x • u - x‖^2 ≤ (d - 1)^2 * ‖x‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_smul, mul_pow, hu]
    change ‖inner ℂ u x‖^2 * d - 2 * (inner ℂ (inner ℂ u x • u) x).re + ‖x‖^2 ≤ _
    rw [hi]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hc)]
  have hn : ‖inner ℂ u x • u - x‖ ≤ (d - 1) * ‖x‖ := by
    have hnonneg := mul_nonneg hd1.le (norm_nonneg x)
    nlinarith [norm_nonneg (inner ℂ u x • u - x)]
  rw [rankOneComplement_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hd1)]
  calc
    _ ≤ (d - 1)⁻¹ * ((d - 1) * ‖x‖) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hd1.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hd1.ne', one_mul]

theorem rankOneComplement_norm_le (d : ℝ) (hd : 2 ≤ d) (u : E) (hu : ‖u‖^2 = d) :
    ‖rankOneComplement d u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using rankOneComplement_contraction d hd u hu x

theorem rankOneComplement_adjoint [CompleteSpace E] (d : ℝ) (u : E) :
    ContinuousLinearMap.adjoint (rankOneComplement d u) = rankOneComplement d u := by
  simp [rankOneComplement, map_smulₛₗ, map_sub, ContinuousLinearMap.adjoint_id]

end Hilbert

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrixHilbertSchmidt_inner_identity (A : Matrix I I ℂ) :
    inner ℂ (matrixHilbertSchmidt (1 : Matrix I I ℂ)) (matrixHilbertSchmidt A) = A.trace := by
  change (∑ ij : I × I, A ij.1 ij.2 * star ((1 : Matrix I I ℂ) ij.1 ij.2)) = _
  simp [Fintype.sum_prod_type, Matrix.one_apply, Matrix.trace]

theorem matrixHilbertSchmidt_identity_norm_sq :
    ‖matrixHilbertSchmidt (1 : Matrix I I ℂ)‖^2 = (Fintype.card I : ℝ) := by
  rw [matrixHilbertSchmidt_norm_sq _ Matrix.isHermitian_one]
  simp

/-- The complex Hilbert–Schmidt operator representing the physical complement. -/
def localComplementHilbert : EuclideanSpace ℂ (I × I) →L[ℂ] EuclideanSpace ℂ (I × I) :=
  rankOneComplement (Fintype.card I : ℝ) (matrixHilbertSchmidt (1 : Matrix I I ℂ))

theorem localComplementHilbert_matrix (A : Matrix I I ℂ) :
    localComplementHilbert (matrixHilbertSchmidt A) =
      matrixHilbertSchmidt (((Fintype.card I : ℂ) - 1)⁻¹ • (A.trace • 1 - A)) := by
  rw [localComplementHilbert, rankOneComplement_apply, matrixHilbertSchmidt_inner_identity]
  ext ij
  simp [matrixHilbertSchmidt]

theorem localComplementHilbert_traceless (A : Matrix I I ℂ) (ht : A.trace = 0) :
    localComplementHilbert (matrixHilbertSchmidt A) =
      (-((Fintype.card I : ℂ) - 1)⁻¹) • matrixHilbertSchmidt A := by
  rw [localComplementHilbert_matrix, ht, zero_smul, zero_sub]
  ext ij
  simp [matrixHilbertSchmidt]

theorem localComplementHilbert_norm_le (hd : 2 ≤ Fintype.card I) :
    ‖localComplementHilbert (I := I)‖ ≤ 1 :=
  rankOneComplement_norm_le _ (by exact_mod_cast hd) _ matrixHilbertSchmidt_identity_norm_sq

theorem localComplement_hilbertSchmidt_contraction (hd : 2 ≤ Fintype.card I)
    (A : Matrix I I ℂ) :
    ‖matrixHilbertSchmidt (((Fintype.card I : ℂ) - 1)⁻¹ • (A.trace • 1 - A))‖ ≤
      ‖matrixHilbertSchmidt A‖ := by
  rw [← localComplementHilbert_matrix]
  exact rankOneComplement_contraction _ (by exact_mod_cast hd) _ matrixHilbertSchmidt_identity_norm_sq _

theorem localComplementHilbert_adjoint :
    ContinuousLinearMap.adjoint (localComplementHilbert (I := I)) = localComplementHilbert :=
  rankOneComplement_adjoint _ _

theorem localComplement_trace (hd : 2 ≤ Fintype.card I) (A : Matrix I I ℂ) :
    ((((Fintype.card I : ℂ) - 1)⁻¹ • (A.trace • 1 - A)) : Matrix I I ℂ).trace = A.trace := by
  have hd0 : (Fintype.card I : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (by omega : Fintype.card I ≠ 1))
  simp only [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, smul_eq_mul]
  field_simp

theorem localComplement_identity (hd : 2 ≤ Fintype.card I) :
    localComplementHilbert (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      matrixHilbertSchmidt (1 : Matrix I I ℂ) := by
  rw [localComplementHilbert_matrix]
  congr 1
  have hd0 : (Fintype.card I : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (by omega : Fintype.card I ≠ 1))
  have he : (Fintype.card I : ℂ) • (1 : Matrix I I ℂ) - 1 =
      ((Fintype.card I : ℂ) - 1) • (1 : Matrix I I ℂ) := by rw [sub_smul, one_smul]
  rw [Matrix.trace_one, he, smul_smul, inv_mul_cancel₀ hd0, one_smul]

theorem localComplement_hermitian (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    ((((Fintype.card I : ℂ) - 1)⁻¹ • (A.trace • 1 - A)) : Matrix I I ℂ).IsHermitian := by
  have ht : IsSelfAdjoint A.trace := by
    rw [IsSelfAdjoint, ← Matrix.trace_conjTranspose, hA.eq]
  have hc : IsSelfAdjoint (((Fintype.card I : ℂ) - 1)⁻¹) := by simp [IsSelfAdjoint]
  exact ((Matrix.isHermitian_one.smul ht).sub hA).smul hc

/-- The same physical operator on the real Hilbert space used by frames. -/
def localComplementRealHilbert : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I) :=
  localComplementHilbert.restrictScalars ℝ

theorem localComplementRealHilbert_norm_le (hd : 2 ≤ Fintype.card I) :
    ‖localComplementRealHilbert (I := I)‖ ≤ 1 := by
  simpa only [localComplementRealHilbert, ContinuousLinearMap.norm_restrictScalars] using
    localComplementHilbert_norm_le hd

theorem localComplementRealHilbert_adjoint :
    ContinuousLinearMap.adjoint (localComplementRealHilbert (I := I)) = localComplementRealHilbert := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hr (a b : EuclideanSpace ℂ (I × I)) : inner ℝ a b = (inner ℂ a b).re := by
    change (∑ i, (b i * star (a i)).re) = (∑ i, b i * star (a i)).re
    rw [Complex.re_sum]
  rw [hr, hr]
  simp only [localComplementRealHilbert, ContinuousLinearMap.coe_restrictScalars']
  have h := ContinuousLinearMap.adjoint_inner_left (localComplementHilbert (I := I)) y x
  rw [localComplementHilbert_adjoint] at h
  exact congrArg Complex.re h.symm

end CertificationGaussian
