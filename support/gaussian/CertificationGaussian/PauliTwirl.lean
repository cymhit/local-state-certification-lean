import CertificationGaussian.PauliBasisRecords
import CertificationGaussian.HaarChangedSiteTensor

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace CertificationGaussian

theorem pauliBasisRecords_complex_integral (f : PauliRecord → ℂ) :
    (∫ ω,f ω ∂pauliBasisRecords)=(1/6:ℂ)*∑ b : Fin 3,∑ j : Fin 2,f (b,j) := by
  have hi : Integrable f pauliBasisRecords :=
    (show Continuous f from continuous_of_discreteTopology).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [pauliBasisRecords,integral_prod _ hi]
  simp_rw [uniformFiniteOutcome_integral]
  norm_num only [Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  ring

@[simp] theorem pauliAmplitude_fourth : pauliAmplitude^4=(1/4:ℂ) := by
  calc
    _ = (pauliAmplitude^2)^2 := by ring
    _ = _ := by rw [pauliAmplitude_sq]; norm_num

/-- The exact full-record Pauli projector first moment. -/
theorem pauliBasisRecords_projector_mean (i j : Fin 2) :
    (2:ℂ)*∫ ω,pauliRecordedProjector ω i j ∂pauliBasisRecords =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  rw [pauliBasisRecords_complex_integral]
  fin_cases i <;> fin_cases j
  all_goals norm_num [pauliRecordedProjector_apply,pauliRecordedUnitVector_apply,
    pauliBasisMatrix,Fin.sum_univ_succ,star_mul,star_neg,Complex.star_def,pauliAmplitude_conj]
  all_goals ring_nf
  all_goals norm_num

/-- True Pauli success twirl for every complex matrix, with the reference-law factor d=2. -/
theorem pauliBasisRecords_success (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (2:ℂ)*∫ ω,pauliRecordedProjector ω i j*Matrix.trace (pauliRecordedProjector ω*A)
      ∂pauliBasisRecords = (A i j + if i=j then Matrix.trace A else 0)/3 := by
  rw [pauliBasisRecords_complex_integral]
  fin_cases i <;> fin_cases j
  all_goals norm_num [Matrix.trace,Matrix.diag,Matrix.mul_apply,pauliRecordedProjector_apply,
    pauliRecordedUnitVector_apply,pauliBasisMatrix,Fin.sum_univ_succ,
    star_mul,star_neg,Complex.star_def,pauliAmplitude_conj]
  all_goals ring_nf
  all_goals norm_num
  all_goals ring

/-- The failure twirl uses the same complete record measure and the actual complementary effect. -/
theorem pauliBasisRecords_complement (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (2:ℂ)*∫ ω,pauliRecordedProjector ω i j*Matrix.trace ((1-pauliRecordedProjector ω)*A)
      ∂pauliBasisRecords = ((if i=j then 2*Matrix.trace A else 0)-A i j)/3 := by
  have hi (f : PauliRecord → ℂ) : Integrable f pauliBasisRecords :=
    (show Continuous f from continuous_of_discreteTopology).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [Matrix.sub_mul,one_mul,Matrix.trace_sub,mul_sub]
  rw [integral_sub (hi _) (hi _),mul_sub,integral_mul_const,
    ← mul_assoc,pauliBasisRecords_projector_mean,pauliBasisRecords_success]
  by_cases hij : i=j <;> simp [hij,Matrix.one_apply]
  all_goals ring

end CertificationGaussian
