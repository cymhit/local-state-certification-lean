import CertificationGaussian.ComplexGaussianMatrixWick

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace CertificationGaussian.Consumers

/-- Complete finite normal-order consumer: actual law, all matrix inputs, true tensor trace and exact count. -/
theorem normal_order_four_matrix_integral {I : Type*} [Fintype I] [DecidableEq I]
    (A : Fin 4 × Fin 2 → Matrix I I ℂ) :
    Integrable (fun x => ∏ b : Fin 4,
      complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x)) (pairedGaussian I) ∧
    (∫ x, ∏ b : Fin 4, complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x)
      ∂pairedGaussian I) =
      ∑ π ∈ fourBlockDerangements, Matrix.trace (wickTensorMatrix A * wickTensorPermutationMatrix π) ∧
    fourBlockDerangements.card=4752 :=
  ⟨complexGaussian_four_matrix_blocks_integrable A,complexGaussian_four_matrix_blocks_trace A,
    fourBlockDerangements_card⟩

/-- The one-dimensional matrix normal product is exactly s^2-4s+2, where s=bar z*z. -/
theorem one_dimensional_normal_matrix (z : Fin 1 → ℂ) :
    complexGaussianNormalMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 z =
      (star (z 0)*z 0)^2-4*(star (z 0)*z 0)+2 := by
  simp [complexGaussianNormalMatrix,sphereQuadraticForm,Matrix.trace,Matrix.diag]
  ring

/-- The actual scalar W fourth moment is 4752, and equals the proved admissible pairing count. -/
theorem one_dimensional_normal_matrix_fourth :
    (∫ x, complexGaussianNormalMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (complexCoordinate x)^4
      ∂pairedGaussian (Fin 1)) = (fourBlockDerangements.card : ℂ) := by
  simp_rw [one_dimensional_normal_matrix]
  rw [complexGaussian_normal_scalar_fourth,fourBlockDerangements_card]
  norm_num

/-- Empty matrix coordinates are allowed; no nonempty premise was introduced by tensor traces. -/
theorem empty_normal_matrix_fourth (A : Fin 4 × Fin 2 → Matrix (Fin 0) (Fin 0) ℂ) :
    (∫ x, ∏ b : Fin 4, complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x)
      ∂pairedGaussian (Fin 0)) = 0 := by
  simp [complexGaussianNormalMatrix,sphereQuadraticForm,Matrix.trace,Matrix.diag]

/-- A genuine non-Hermitian input for the arbitrary-complex-matrix identity. -/
def normalWickNilpotent : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]

theorem normalWickNilpotent_not_hermitian : ¬normalWickNilpotent.IsHermitian := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h.eq
  norm_num [normalWickNilpotent,Matrix.conjTranspose_apply] at he

/-- With a nilpotent input the two quadratic correction terms vanish, as the actual matrices dictate. -/
theorem normalWickNilpotent_value (z : Fin 2 → ℂ) :
    complexGaussianNormalMatrix normalWickNilpotent normalWickNilpotent z =
      (star (z 0)*z 1)^2 := by
  norm_num [complexGaussianNormalMatrix,sphereQuadraticForm,normalWickNilpotent,
    Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]
  ring

/-- The complete integral identity really applies to four non-Hermitian matrix pairs. -/
theorem normalWickNilpotent_four_blocks :
    (∫ x, (star (complexCoordinate x (0 : Fin 2))*complexCoordinate x 1)^8
      ∂pairedGaussian (Fin 2)) =
      ∑ π ∈ fourBlockDerangements,
        Matrix.trace (wickTensorMatrix (fun _ : Fin 4 × Fin 2 => normalWickNilpotent) *
          wickTensorPermutationMatrix π) := by
  have h := complexGaussian_four_matrix_blocks_trace (fun _ : Fin 4 × Fin 2 => normalWickNilpotent)
  simpa only [normalWickNilpotent_value,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← pow_mul,show 2*4=8 by decide] using h

/-- The non-Hermitian nilpotent fourth block product has actual Gaussian expectation zero. -/
theorem normalWickNilpotent_fourth_zero :
    (∫ x, complexGaussianNormalMatrix normalWickNilpotent normalWickNilpotent (complexCoordinate x)^4
      ∂pairedGaussian (Fin 2)) = 0 := by
  have h := complexGaussian_balanced_wick_integral 8 (fun _ : Fin 8 => (0 : Fin 2))
    (fun _ : Fin 8 => (1 : Fin 2))
  have hne : (0 : Fin 2) ≠ 1 := by decide
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,ite_eq_right hne,
    zero_pow (by decide : 8 ≠ 0),Finset.sum_const_zero] at h
  simpa only [normalWickNilpotent_value,← pow_mul,show 2*4=8 by decide,mul_pow] using h

end CertificationGaussian.Consumers
