import CertificationGaussian.BellPartialTranspose
import CertificationGaussian.Consumers.UnitaryGaussianChaos

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- The genuinely non-Hermitian phase unitary has the exact normalized Bell partial-transpose norm. -/
theorem nonhermitian_bell_partialTranspose_norm :
    ‖Matrix.toEuclideanCLM (n:=Fin 2 × Fin 2) (𝕜:=ℂ)
      (partialTransposeFirst (unitaryBellProjector (signedUnitaryFamily 0)))‖=(1/2:ℝ) := by
  simpa using unitaryBellProjector_partialTranspose_norm (signedUnitaryFamily 0)
    (signedUnitaryFamily_unitary 0)

/-- The incomplete signed family is bounded using its actual coefficient mass, with no individual Hermiticity premise. -/
theorem signed_bell_partialTranspose_bound :
    ‖Matrix.toEuclideanCLM (n:=Fin 2 × Fin 2) (𝕜:=ℂ)
      (partialTransposeFirst (weightedBellMatrix signedUnitaryFamily signedUnitaryWeights))‖≤(5/2:ℝ) := by
  have h := weightedBell_partialTranspose_norm_le signedUnitaryFamily signedUnitaryWeights signedUnitaryFamily_unitary
  norm_num [signedUnitaryWeights,Fin.sum_univ_two] at h
  exact h

/-- Removing the actual negative-weight phase term costs at most one in the true partial-transpose norm. -/
theorem signed_bell_remove_phase_bound :
    ‖Matrix.toEuclideanCLM (n:=Fin 2 × Fin 2) (𝕜:=ℂ)
      (partialTransposeFirst (weightedBellMatrix signedUnitaryFamily signedUnitaryWeights)-
        partialTransposeFirst (weightedBellMatrix signedUnitaryFamily
          (fun w => if w=0 then 0 else signedUnitaryWeights w)))‖≤(1:ℝ) := by
  have h := weightedBell_partialTranspose_remove_bound signedUnitaryFamily signedUnitaryWeights
    signedUnitaryFamily_unitary ({0}:Finset (Fin 2))
  simpa [signedUnitaryWeights] using h

/-- The actual finite-removal bound is dimension and family general, with no completeness or orthogonality requirement. -/
theorem finite_bell_removal (D m : ℕ) (W : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (a : Fin m → ℝ) (hW : ∀ w,W w∈unitary (Matrix (Fin D) (Fin D) ℂ)) (F : Finset (Fin m)) :
    ‖Matrix.toEuclideanCLM (n:=Fin D × Fin D) (𝕜:=ℂ)
      (partialTransposeFirst (weightedBellMatrix W a)-
        partialTransposeFirst (weightedBellMatrix W (fun w => if w∈F then 0 else a w)))‖≤
      (F.card:ℝ)*‖a‖/(D:ℝ) := by
  simpa only [Fintype.card_fin] using weightedBell_partialTranspose_remove_card_bound W a hW F

/-- Empty-coordinate Bell partial transpose has norm zero, consistently with the total inverse convention. -/
theorem empty_bell_partialTranspose_norm :
    ‖Matrix.toEuclideanCLM (n:=Fin 0 × Fin 0) (𝕜:=ℂ)
      (partialTransposeFirst (unitaryBellProjector (0:Matrix (Fin 0) (Fin 0) ℂ)))‖=0 := by
  have hU : (0:Matrix (Fin 0) (Fin 0) ℂ)∈unitary (Matrix (Fin 0) (Fin 0) ℂ) := by
    constructor <;> ext i j <;> exact Fin.elim0 i
  simpa only [Fintype.card_fin,Nat.cast_zero,_root_.inv_zero] using unitaryBellProjector_partialTranspose_norm _ hU

end CertificationGaussian.Consumers
