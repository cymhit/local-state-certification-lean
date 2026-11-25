import CertificationGaussian.HaarBasisRecords

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CertificationGaussian.Consumers

/-- The complete record projector is the exact coordinate-POVM compression by U†. -/
theorem haar_record_coordinate_effect (d : Nat)
    (ω : ComplexUnitary (Fin d) × Fin d) :
    recordedProjector d ω =
      ω.1.val*Matrix.single ω.2 ω.2 (1:ℂ)*ω.1.val.conjTranspose :=
  columnProjector_eq_conjugate_single (Fin d) ω.1.val ω.2

/-- Both actual Haar-record channel identities hold for every complex input, including non-Hermitian ones. -/
theorem local_haar_twirl_pair (d : Nat) [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    ((d:ℂ)*∫ ω, recordedProjector d ω a b*Matrix.trace (recordedProjector d ω*A)
      ∂haarBasisRecords d = (A a b + if a=b then Matrix.trace A else 0)/((d:ℂ)+1)) ∧
    ((d:ℂ)*∫ ω, recordedProjector d ω a b*Matrix.trace ((1-recordedProjector d ω)*A)
      ∂haarBasisRecords d =
      (((d:ℂ)*Matrix.trace A)*(if a=b then 1 else 0)-A a b)/((d:ℂ)+1)) :=
  ⟨haarBasisRecords_success d A a b, haarBasisRecords_complement d A a b⟩

/-- In dimension one the success channel is identity and the complement vanishes. -/
theorem dimension_one_local_haar (A : Matrix (Fin 1) (Fin 1) ℂ) :
    (∫ ω, recordedProjector 1 ω 0 0*Matrix.trace (recordedProjector 1 ω*A)
      ∂haarBasisRecords 1 = A 0 0) ∧
    (∫ ω, recordedProjector 1 ω 0 0*Matrix.trace ((1-recordedProjector 1 ω)*A)
      ∂haarBasisRecords 1 = 0) := by
  have h := local_haar_twirl_pair 1 A 0 0
  norm_num [Matrix.trace, Matrix.diag] at h
  simpa [Matrix.trace, Matrix.diag] using h

/-- At d=2 the exact Haar denominators are 3; this does not assert a finite three-basis cubature. -/
theorem qubit_local_haar (A : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    (2:ℂ)*∫ ω, recordedProjector 2 ω a b*Matrix.trace (recordedProjector 2 ω*A)
      ∂haarBasisRecords 2 = (A a b + if a=b then Matrix.trace A else 0)/3 := by
  have h := haarBasisRecords_success 2 A a b
  norm_num at h
  exact h

end CertificationGaussian.Consumers
