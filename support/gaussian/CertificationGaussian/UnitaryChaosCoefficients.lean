import CertificationGaussian.ComplexGaussianDecoupling
import Mathlib.Data.Matrix.Basis

noncomputable section
open Matrix Finset MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

/-- The normalized conjugation coefficient of a real weighted unitary family.
Individual family matrices need not be Hermitian. -/
def unitaryChaosCoefficient (W : K → Matrix I I ℂ) (a : K → ℝ) (i j : I) : Matrix I I ℂ :=
  (Fintype.card I:ℂ)⁻¹ • ∑ w, (a w:ℂ) • (W w * Matrix.single i j (1:ℂ) * (W w)ᴴ)

omit [Fintype K] [DecidableEq K] in
theorem matrix_unit_sandwich_apply (A B : Matrix I I ℂ) (i j r s : I) :
    (A * Matrix.single i j (1:ℂ) * B) r s = A r i * B j s := by
  simp [Matrix.mul_apply, Matrix.single, ite_and]

omit [DecidableEq K] in
theorem unitaryChaosCoefficient_apply (W : K → Matrix I I ℂ) (a : K → ℝ)
    (i j r s : I) :
    unitaryChaosCoefficient W a i j r s =
      (Fintype.card I:ℂ)⁻¹ * ∑ w, (a w:ℂ) * W w r i * star (W w s j) := by
  simp only [unitaryChaosCoefficient, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    matrix_unit_sandwich_apply, Matrix.conjTranspose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  ring

omit [Fintype K] [DecidableEq K] in
/-- Exact matrix-unit contraction underlying the two Gaussian covariance identities. -/
theorem matrix_units_trace_identity (A : Matrix I I ℂ) :
    ∑ i, ∑ j, Matrix.single i j (1:ℂ) * A * Matrix.single j i (1:ℂ) = Matrix.trace A • (1 : Matrix I I ℂ) := by
  simp only [Matrix.single_mul_mul_single, one_mul, mul_one]
  ext r s
  simp [Matrix.sum_apply, Matrix.single, Matrix.trace, Matrix.one_apply, ite_and, eq_comm]

omit [DecidableEq K] in
/-- The coefficient adjoint swaps Gaussian indices because the weights are real. -/
theorem unitaryChaosCoefficient_adjoint (W : K → Matrix I I ℂ) (a : K → ℝ) (i j : I) :
    (unitaryChaosCoefficient W a i j)ᴴ = unitaryChaosCoefficient W a j i := by
  ext r s
  simp only [Matrix.conjTranspose_apply, unitaryChaosCoefficient_apply,
    star_mul, star_inv₀, star_sum, star_star]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_natCast]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  ring

omit [DecidableEq K] in
/-- The true diagonal mean of the conjugation coefficients. -/
theorem unitaryChaosCoefficient_diagonal_sum (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ)) :
    ∑ i, unitaryChaosCoefficient W a i i =
      ((∑ w, (a w:ℂ))/(Fintype.card I:ℂ)) • (1 : Matrix I I ℂ) := by
  ext r s
  simp only [Matrix.sum_apply, unitaryChaosCoefficient_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hu (w : K) : ∑ i, W w r i * star (W w s i) = (1 : Matrix I I ℂ) r s := by
    have h := congrArg (fun M : Matrix I I ℂ => M r s) (Unitary.mul_star_self_of_mem (hW w))
    change (W w * (W w)ᴴ) r s = (1 : Matrix I I ℂ) r s at h
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  simp_rw [mul_assoc, ← Finset.mul_sum, hu]
  rw [← Finset.sum_mul]
  ring

omit [Fintype K] [DecidableEq K] in
/-- The mixed covariance contracts to the Hilbert-Schmidt inner product of two matrices. -/
theorem matrix_unit_conjugation_cross (U V : Matrix I I ℂ) :
    ∑ i, ∑ j, (U * Matrix.single i j (1:ℂ) * Uᴴ) *
      (V * Matrix.single j i (1:ℂ) * Vᴴ) =
      Matrix.trace (Uᴴ * V) • (U * Vᴴ) := by
  have ht (i j : I) : (U * Matrix.single i j (1:ℂ) * Uᴴ) *
      (V * Matrix.single j i (1:ℂ) * Vᴴ) =
      U * (Matrix.single i j (1:ℂ) * (Uᴴ*V) * Matrix.single j i (1:ℂ)) * Vᴴ := by
    simp only [Matrix.mul_assoc]
  simp_rw [ht]
  simp_rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  rw [matrix_units_trace_identity]
  simp

omit [DecidableEq K] in
theorem unitaryChaosCoefficient_eq_sum (W : K → Matrix I I ℂ) (a : K → ℝ) (i j : I) :
    unitaryChaosCoefficient W a i j =
      ∑ w, ((a w:ℂ)/(Fintype.card I:ℂ)) • (W w * Matrix.single i j (1:ℂ) * (W w)ᴴ) := by
  simp only [unitaryChaosCoefficient, Finset.smul_sum, smul_smul, div_eq_mul_inv, mul_comm]

omit [DecidableEq I] [DecidableEq K] in
theorem finite_sum_four_reorder {M : Type*} [AddCommMonoid M] (f : I → I → K → K → M) :
    ∑ i, ∑ j, ∑ w, ∑ v, f i j w v = ∑ w, ∑ v, ∑ i, ∑ j, f i j w v := by
  calc
    _ = ∑ i, ∑ w, ∑ j, ∑ v, f i j w v := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ w, ∑ i, ∑ j, ∑ v, f i j w v := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      calc
        _ = ∑ i, ∑ v, ∑ j, f i j w v := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

omit [DecidableEq K] in
/-- Expansion and matrix-unit contraction of a weighted family before using orthogonality. -/
theorem weighted_unitary_conjugation_cross (W : K → Matrix I I ℂ) (c : K → ℂ) :
    ∑ i, ∑ j, (∑ w, c w • (W w * Matrix.single i j (1:ℂ) * (W w)ᴴ)) *
      (∑ v, c v • (W v * Matrix.single j i (1:ℂ) * (W v)ᴴ)) =
      ∑ w, ∑ v, (c w*c v*Matrix.trace ((W w)ᴴ*W v)) • (W w*(W v)ᴴ) := by
  simp only [Matrix.sum_mul]
  simp only [Matrix.mul_sum]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [finite_sum_four_reorder]
  simp_rw [← Finset.smul_sum, matrix_unit_conjugation_cross, smul_smul]
  simp only [mul_assoc, mul_comm]

/-- The first Gram matrix is a scalar identity for every unitary Hilbert-Schmidt orthogonal family. -/
theorem unitaryChaosCoefficient_leftGram [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    ∑ i, ∑ j, unitaryChaosCoefficient W a i j * (unitaryChaosCoefficient W a i j)ᴴ =
      ((∑ w, (a w:ℂ)^2)/(Fintype.card I:ℂ)) • (1 : Matrix I I ℂ) := by
  have hD : (Fintype.card I:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hu (w : K) : W w * (W w)ᴴ = 1 := Unitary.mul_star_self_of_mem (hW w)
  have hc (w : K) : ((a w:ℂ)/(Fintype.card I:ℂ))*((a w:ℂ)/(Fintype.card I:ℂ))*(Fintype.card I:ℂ) =
      (a w:ℂ)^2/(Fintype.card I:ℂ) := by field_simp
  simp_rw [unitaryChaosCoefficient_adjoint, unitaryChaosCoefficient_eq_sum]
  rw [weighted_unitary_conjugation_cross]
  simp only [hHS, mul_ite, mul_zero, ite_smul, zero_smul]
  simp [hu, hc, ← Finset.sum_smul, ← Finset.sum_div]

/-- The second Gram has the same scalar, by the exact real-weight adjoint relation. -/
theorem unitaryChaosCoefficient_rightGram [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w, W w ∈ unitary (Matrix I I ℂ))
    (hHS : ∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (Fintype.card I:ℂ) else 0) :
    ∑ i, ∑ j, (unitaryChaosCoefficient W a i j)ᴴ * unitaryChaosCoefficient W a i j =
      ((∑ w, (a w:ℂ)^2)/(Fintype.card I:ℂ)) • (1 : Matrix I I ℂ) := by
  rw [← unitaryChaosCoefficient_leftGram W a hW hHS, Finset.sum_comm]
  simp only [unitaryChaosCoefficient_adjoint]

end CertificationGaussian
