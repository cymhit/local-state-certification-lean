import LocalCertification.Quantum.WeylShellState
import LocalCertification.Quantum.UniformProductBasis
import QIT.Core.POVMProbability

open scoped BigOperators ComplexOrder
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The existing QIT coordinate POVM, conjugated to the actual unitary basis. -/
def basisPOVM (U : ↥(unitary (Matrix I I ℂ))) : QIT.POVM I I :=
  (QIT.POVM.coordinate I).compressByIsometry U.val.conjTranspose (by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose] using U.property.2)

theorem basisPOVM_effect (U : ↥(unitary (Matrix I I ℂ))) (x : I) :
    (basisPOVM U).effects x = U.val * Matrix.single x x (1 : ℂ) * U.val.conjTranspose := by
  simp [basisPOVM]

theorem basisPOVM_effect_rankOne (U : ↥(unitary (Matrix I I ℂ))) (x : I) :
    (basisPOVM U).effects x = QIT.rankOneMatrix (fun i => U.val i x) := by
  rw [basisPOVM_effect]
  ext i j
  simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]

theorem basisPOVM_effect_trace (U : ↥(unitary (Matrix I I ℂ))) (x : I) :
    ((basisPOVM U).effects x).trace = 1 := by
  rw [basisPOVM_effect_rankOne, QIT.rankOneMatrix_trace]
  have h := congrArg (fun M : Matrix I I ℂ => M x x) U.property.1
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    dotProduct, mul_comm] using h

/-- QIT's nonnegative Born probability, with its proved completeness law. -/
def basisBorn (U : ↥(unitary (Matrix I I ℂ))) (ρ : QIT.State I) (x : I) : ℝ :=
  (basisPOVM U).prob ρ x

theorem basisBorn_nonneg (U : ↥(unitary (Matrix I I ℂ))) (ρ : QIT.State I) (x : I) :
    0 ≤ basisBorn U ρ x := (QIT.POVM.prob (basisPOVM U) ρ x).coe_nonneg

theorem basisBorn_sum (U : ↥(unitary (Matrix I I ℂ))) (ρ : QIT.State I) :
    ∑ x, basisBorn U ρ x = 1 := by
  unfold basisBorn
  exact_mod_cast (basisPOVM U).sum_prob ρ

theorem basisBorn_trace (U : ↥(unitary (Matrix I I ℂ))) (ρ : QIT.State I) (x : I) :
    basisBorn U ρ x = (ρ.matrix * (basisPOVM U).effects x).trace.re :=
  (basisPOVM U).prob_eq_trace_re ρ x

theorem basisBorn_diagonal (U : ↥(unitary (Matrix I I ℂ))) (ρ : QIT.State I) (x : I) :
    basisBorn U ρ x = ((U.val.conjTranspose * ρ.matrix * U.val) x x).re := by
  rw [basisBorn_trace, basisPOVM_effect]
  congr 1
  calc
    (ρ.matrix * (U.val * Matrix.single x x (1 : ℂ) * U.val.conjTranspose)).trace =
        ((U.val.conjTranspose * ρ.matrix * U.val) * Matrix.single x x (1 : ℂ)).trace := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (ρ.matrix * U.val * Matrix.single x x (1 : ℂ)) U.val.conjTranspose
    _ = _ := by rw [Matrix.trace_mul_single]; simp

omit [DecidableEq I] in
/-- A short rank-one transport bridge, using the same QIT kernel definition. -/
theorem matrix_conjugate_rankOne (M : Matrix I I ℂ) (v : I → ℂ) :
    M * QIT.rankOneMatrix v * M.conjTranspose = QIT.rankOneMatrix (M.mulVec v) := by
  simp only [QIT.rankOneMatrix, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  ext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose, mul_comm]

theorem basisBorn_pure (U : ↥(unitary (Matrix I I ℂ))) (ψ : QIT.PureVector I) (x : I) :
    basisBorn U ψ.state x = Complex.normSq (U.val.conjTranspose.mulVec ψ.amp x) := by
  rw [basisBorn_diagonal]
  change ((U.val.conjTranspose * QIT.rankOneMatrix ψ.amp * U.val) x x).re = _
  have h := matrix_conjugate_rankOne U.val.conjTranspose ψ.amp
  simp only [Matrix.conjTranspose_conjTranspose] at h
  rw [h]
  simp [QIT.rankOneMatrix_apply, Complex.mul_conj]

/-- Actual products of the local unitaries define a genuine QIT POVM on the sole tensor index. -/
def productBasisPOVM (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d) :
    QIT.POVM (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) :=
  basisPOVM ⟨CertificationGaussian.tensorUnitaryMatrix d n U, CertificationGaussian.tensorUnitaryMatrix_unitary d n U⟩

theorem productBasisPOVM_effect (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (x : CertificationGaussian.QuditIndex d n) :
    (productBasisPOVM d n U).effects x =
      tensorMatrix (fun i => (basisPOVM (U i)).effects (x i)) := by
  rw [productBasisPOVM, basisPOVM_effect_rankOne]
  simp_rw [basisPOVM_effect_rankOne]
  ext a b
  simp only [QIT.rankOneMatrix_apply, CertificationGaussian.tensorUnitaryMatrix, tensorMatrix,
    star_prod, Finset.prod_mul_distrib]

def productBorn (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (x : CertificationGaussian.QuditIndex d n) : ℝ :=
  (productBasisPOVM d n U).prob ρ x

theorem productBorn_nonneg (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (x : CertificationGaussian.QuditIndex d n) :
    0 ≤ productBorn d n U ρ x := (QIT.POVM.prob (productBasisPOVM d n U) ρ x).coe_nonneg

theorem productBorn_sum (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    ∑ x, productBorn d n U ρ x = 1 := by
  unfold productBorn
  exact_mod_cast (productBasisPOVM d n U).sum_prob ρ

/-- The QIT Born probability is exactly the U-dagger coordinate used in the probability bounds. -/
theorem productBorn_pure (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U ψ.state x =
      Complex.normSq ((tensorBasis d n (qitProductBasis d n U)).conjTranspose.mulVec ψ.amp x) := by
  rw [tensorBasis_qitProductBasis]
  exact basisBorn_pure
    ⟨CertificationGaussian.tensorUnitaryMatrix d n U, CertificationGaussian.tensorUnitaryMatrix_unitary d n U⟩ ψ x

end LocalCertification.Quantum
