import CertificationGaussian.FourRecordTensorAverage

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator Kronecker
namespace CertificationGaussian

/-- The original complex contraction, retaining each full basis/outcome record and all eight input choices. -/
def recordedChangedSiteIntegrand {Ω : Type*} (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (a : Fin 4 × Fin 2 → Bool)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (x : Ω × (Ω × (Ω × Ω))) : ℂ :=
  Matrix.trace (recordedProjector d (r x.1)*recordedProjector d (r x.2.1)*
    recordedProjector d (r x.2.2.1)*recordedProjector d (r x.2.2.2))*
  Matrix.trace (wickTensorMatrix (fun t : Fin 4 × Fin 2 =>
    localReadoutFactor d (a t) (r (fourRecordAt x t.1)))*wickTensorPermutationMatrix π)

/-- The original complex contraction is the trace of the actual twelve-slot tensor against its genuine permutation. -/
theorem recordedChangedSiteIntegrand_eq_tensor {Ω : Type*} (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (a : Fin 4 × Fin 2 → Bool)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (x : Ω × (Ω × (Ω × Ω))) :
    recordedChangedSiteIntegrand d r a π x =
      Matrix.trace (wickTensorMatrix (fun b : Fin 4 =>
        localChangedSiteIntegrand d (a (b,0)) (a (b,1)) (r (fourRecordAt x b)))*
          combinedWickPermutationMatrix π) := by
  symm
  simpa [localChangedSiteIntegrand,recordedChangedSiteIntegrand,fourRecordAt] using
    combinedWickPermutationMatrix_actual_trace
      (fun t : Fin 4 × Fin 2 => localReadoutFactor d (a t) (r (fourRecordAt x t.1)))
      (fun b : Fin 4 => recordedProjector d (r (fourRecordAt x b))) π

@[fun_prop] theorem recordedChangedSiteIntegrand_continuous {Ω : Type*} [TopologicalSpace Ω]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (a : Fin 4 × Fin 2 → Bool) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Continuous (recordedChangedSiteIntegrand d r a π) := by
  simp_rw [funext (recordedChangedSiteIntegrand_eq_tensor d r a π)]
  simp only [wickTensorMatrix,Matrix.trace,Matrix.diag,Matrix.mul_apply]
  fun_prop

section CompactRecords
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [SecondCountableTopology Ω]

/-- The actual four-record integral, with d^4 normalization, equals the tensor of four true local Bochner averages. -/
theorem recordedChangedSiteIntegral_eq_tensor (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (a : Fin 4 × Fin 2 → Bool) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    (d:ℂ)^4*(∫ x,recordedChangedSiteIntegrand d r a π x ∂fourReadoutLaw μ) =
      Matrix.trace (wickTensorMatrix (fun b : Fin 4 => (d:ℝ) •
        ∫ s,localChangedSiteIntegrand d (a (b,0)) (a (b,1)) (r s) ∂μ)*
          combinedWickPermutationMatrix π) := by
  rw [wickTensorMatrix_four_scaled_trace]
  simp only [Complex.ofReal_natCast]
  congr 1
  simp_rw [recordedChangedSiteIntegrand_eq_tensor]
  exact fourReadout_tensor_trace_integral μ
    (fun b s => localChangedSiteIntegrand d (a (b,0)) (a (b,1)) (r s))
    (fun b => (localChangedSiteIntegrand_continuous d _ _).comp hr) _

end CompactRecords

/-- The original Haar changed-site contraction under the same complete-record law. -/
def haarChangedSiteIntegrand (d : ℕ) (a : Fin 4 × Fin 2 → Bool)
    (π : Equiv.Perm (Fin 4 × Fin 2)) := recordedChangedSiteIntegrand d id a π

theorem haarChangedSiteIntegrand_integrable (d : ℕ) [NeZero d]
    (a : Fin 4 × Fin 2 → Bool) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Integrable (haarChangedSiteIntegrand d a π) (fourReadoutLaw (haarBasisRecords d)) := by
  let : BorelSpace (ComplexUnitary (Fin d) × Fin d) := inferInstance
  let : SecondCountableTopology (ComplexUnitary (Fin d) × Fin d) := inferInstance
  exact (recordedChangedSiteIntegrand_continuous d id continuous_id a π
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem haarChangedSiteIntegral_eq_tensor (d : ℕ) [NeZero d]
    (a : Fin 4 × Fin 2 → Bool) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    (d:ℂ)^4*(∫ x,haarChangedSiteIntegrand d a π x ∂fourReadoutLaw (haarBasisRecords d)) =
      Matrix.trace (wickTensorMatrix (fun b : Fin 4 => haarChangedSiteTensor d (a (b,0)) (a (b,1)))*
        combinedWickPermutationMatrix π) :=
  recordedChangedSiteIntegral_eq_tensor (haarBasisRecords d) d id continuous_id a π

/-- The original Haar integral has the proved cost C_d; no positivity or contraction hypothesis remains. -/
theorem haarChangedSiteContraction_le (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a : Fin 4 × Fin 2 → Bool) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    ‖(d:ℂ)^4*(∫ x,haarChangedSiteIntegrand d a π x ∂fourReadoutLaw (haarBasisRecords d))‖ ≤
      (d:ℝ)^4*((d:ℝ)-1)^8 := by
  rw [haarChangedSiteIntegral_eq_tensor]
  exact haarChangedSite_four_unitary_bound d hd (fun b => a (b,0)) (fun b => a (b,1))
    _ (combinedWickPermutationMatrix_unitary π)

/-- The original Pauli changed-site contraction retains the actual six complete records. -/
def pauliChangedSiteIntegrand (a : Fin 4 × Fin 2 → Bool) (π : Equiv.Perm (Fin 4 × Fin 2)) :=
  recordedChangedSiteIntegrand 2 pauliFullRecord a π

theorem pauliChangedSiteIntegrand_integrable
    (a : Fin 4 × Fin 2 → Bool) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Integrable (pauliChangedSiteIntegrand a π) (fourReadoutLaw pauliBasisRecords) :=
  (recordedChangedSiteIntegrand_continuous 2 pauliFullRecord continuous_of_discreteTopology a π
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem pauliChangedSiteIntegral_eq_tensor (a : Fin 4 × Fin 2 → Bool)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    (16:ℂ)*(∫ x,pauliChangedSiteIntegrand a π x ∂fourReadoutLaw pauliBasisRecords) =
      Matrix.trace (wickTensorMatrix (fun b : Fin 4 => pauliChangedSiteTensor (a (b,0)) (a (b,1)))*
        combinedWickPermutationMatrix π) := by
  have h := recordedChangedSiteIntegral_eq_tensor pauliBasisRecords 2 pauliFullRecord
    continuous_of_discreteTopology a π
  norm_num only [Nat.cast_ofNat,show (2:ℂ)^4=16 by norm_num] at h
  exact h

/-- The same actual six-record Pauli integral has cost 16 for every input choice and permutation. -/
theorem pauliChangedSiteContraction_le (a : Fin 4 × Fin 2 → Bool)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    ‖(16:ℂ)*(∫ x,pauliChangedSiteIntegrand a π x ∂fourReadoutLaw pauliBasisRecords)‖≤16 := by
  rw [pauliChangedSiteIntegral_eq_tensor]
  exact pauliChangedSite_four_unitary_bound (fun b => a (b,0)) (fun b => a (b,1))
    _ (combinedWickPermutationMatrix_unitary π)

end CertificationGaussian
