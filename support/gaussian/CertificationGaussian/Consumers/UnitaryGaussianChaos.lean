import CertificationGaussian.UnitaryGaussianChaos

noncomputable section
open Matrix MeasureTheory Finset
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- One absolute constant precedes all dimensions, family sizes, signed weights and actual unitary families. -/
theorem unitary_gaussian_universal_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (D m : ℕ) (_hD : 0 < D) (W : Fin m → Matrix (Fin D) (Fin D) ℂ) (a : Fin m → ℝ),
      (∀ w, W w ∈ unitary (Matrix (Fin D) (Fin D) ℂ)) →
      (∀ w v, Matrix.trace ((W w)ᴴ*W v) = if w=v then (D:ℂ) else 0) →
      (∫ x, ‖unitaryGaussianConjugation W a x -
        rectangularEuclideanCLM (((∑ w, (a w:ℂ))/(D:ℂ)) • (1 : Matrix (Fin D) (Fin D) ℂ))‖
        ∂pairedGaussian (Fin D)) ≤ C * Real.log (2*(D:ℝ)) *
          max (Real.sqrt ((∑ w, (a w)^2)/(D:ℝ)))
            (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix W a))‖) := by
  refine ⟨8*gaussianMatrixChaosConstant, mul_pos (by norm_num) gaussianMatrixChaosConstant_pos, ?_⟩
  intro D m hD W a hW hHS
  let : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  simpa only [unitaryWeightSquareMean, Fintype.card_fin] using
    unitaryGaussianConjugation_expectation_bound W a hW (by simpa using hHS)

/-- An incomplete HS family with a genuinely non-Hermitian member. -/
def signedUnitaryFamily (w : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if w=0 then !![Complex.I,0;0,Complex.I] else !![0,1;1,0]

def signedUnitaryWeights : Fin 2 → ℝ := ![-2,3]

theorem signedUnitaryFamily_unitary (w : Fin 2) :
    signedUnitaryFamily w ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  change signedUnitaryFamily w ∈ Matrix.unitaryGroup (Fin 2) ℂ
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases w <;> fin_cases i <;> fin_cases j <;>
    norm_num [signedUnitaryFamily, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem signedUnitaryFamily_hilbertSchmidt (w v : Fin 2) :
    Matrix.trace ((signedUnitaryFamily w)ᴴ*signedUnitaryFamily v) = if w=v then (2:ℂ) else 0 := by
  fin_cases w <;> fin_cases v <;>
    norm_num [signedUnitaryFamily, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem signedUnitaryFamily_not_individually_hermitian : ¬(signedUnitaryFamily 0).IsHermitian := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h.eq
  norm_num [signedUnitaryFamily, Matrix.conjTranspose_apply] at he
  have hi := congrArg Complex.im he
  norm_num at hi

theorem signedUnitaryWeights_norm : ‖signedUnitaryWeights‖ = 3 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 3)).mpr
    intro w
    fin_cases w <;> norm_num [signedUnitaryWeights]
  · have h := norm_le_pi_norm signedUnitaryWeights (1:Fin 2)
    norm_num [signedUnitaryWeights] at h ⊢
    exact h


theorem signedUnitaryWeights_sum : (∑ w, (signedUnitaryWeights w:ℂ)) = 1 := by
  norm_num [signedUnitaryWeights, Fin.sum_univ_two]

/-- Both Gram scales and the exact Bell norm for signed weights and a non-Hermitian unitary member. -/
theorem signed_family_three_controls :
    unitaryWeightSquareMean (I := Fin 2) signedUnitaryWeights = 13/2 ∧
    ‖rectangularEuclideanCLM (weightedBellMatrix signedUnitaryFamily signedUnitaryWeights)‖ = 3 ∧
    (∫ x, unitaryGaussianConjugation signedUnitaryFamily signedUnitaryWeights x ∂pairedGaussian (Fin 2)) =
      rectangularEuclideanCLM ((1/2:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨by norm_num [unitaryWeightSquareMean, signedUnitaryWeights, Fin.sum_univ_two], ?_, ?_⟩
  · rw [weightedBellMatrix_norm signedUnitaryFamily signedUnitaryWeights
      (by simpa using signedUnitaryFamily_hilbertSchmidt), signedUnitaryWeights_norm]
  · have h := unitaryGaussianConjugation_mean signedUnitaryFamily signedUnitaryWeights signedUnitaryFamily_unitary
    rw [signedUnitaryWeights_sum] at h
    convert h using 1
    norm_num

theorem signed_family_actual_expectation :
    (∫ x, ‖unitaryGaussianConjugation signedUnitaryFamily signedUnitaryWeights x -
      rectangularEuclideanCLM ((1/2:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))‖ ∂pairedGaussian (Fin 2)) ≤
      (8*gaussianMatrixChaosConstant) * Real.log 4 *
        max (Real.sqrt (13/2)) (max 3 ‖rectangularEuclideanCLM
          (partialTransposeFirst (weightedBellMatrix signedUnitaryFamily signedUnitaryWeights))‖) := by
  have h := unitaryGaussianConjugation_expectation_bound signedUnitaryFamily signedUnitaryWeights
    signedUnitaryFamily_unitary (by simpa using signedUnitaryFamily_hilbertSchmidt)
  rw [signedUnitaryWeights_norm, signed_family_three_controls.1, signedUnitaryWeights_sum] at h
  convert h using 1 <;> norm_num

theorem zero_unitary_weights (D m : ℕ) (W : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin 2 × Fin D → ℝ) : unitaryGaussianConjugation W (fun _ => 0) x = 0 ∧
      weightedBellMatrix W (fun _ => 0) = 0 := by
  simp [unitaryGaussianConjugation, unitaryWeightedRankOne, weightedBellMatrix, rectangularEuclideanCLM]

theorem empty_unitary_family (D : ℕ) (W : Fin 0 → Matrix (Fin D) (Fin D) ℂ) (a : Fin 0 → ℝ)
    (x : Fin 2 × Fin D → ℝ) : unitaryGaussianConjugation W a x = 0 ∧ weightedBellMatrix W a = 0 := by
  simp [unitaryGaussianConjugation, unitaryWeightedRankOne, weightedBellMatrix, rectangularEuclideanCLM]

theorem empty_unitary_dimension (m : ℕ) (W : Fin m → Matrix (Fin 0) (Fin 0) ℂ) (a : Fin m → ℝ)
    (x : Fin 2 × Fin 0 → ℝ) : unitaryGaussianConjugation W a x = 0 := Subsingleton.elim _ _

end CertificationGaussian.Consumers
