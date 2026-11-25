import CertificationGaussian.IncidentHolderContractions
import CertificationGaussian.RankOneWickContraction
import CertificationGaussian.WickFourVertexGraph
import CertificationGaussian.PauliGraphKappa

noncomputable section
open MeasureTheory Matrix Metric Set
open scoped BigOperators
namespace CertificationGaussian

/-- The four complete records in their original block order. -/
def fourRecordAt {Ω : Type*} (x : Ω × (Ω × (Ω × Ω))) : Fin 4 → Ω :=
  ![x.1,x.2.1,x.2.2.1,x.2.2.2]

@[fun_prop] theorem fourRecordAt_continuous {Ω : Type*} [TopologicalSpace Ω] (i : Fin 4) :
    Continuous (fun x : Ω × (Ω × (Ω × Ω)) => fourRecordAt x i) := by
  fin_cases i
  · exact continuous_fst
  · exact continuous_fst.comp continuous_snd
  · exact continuous_fst.comp (continuous_snd.comp continuous_snd)
  · exact continuous_snd.comp (continuous_snd.comp continuous_snd)

variable {Ω I : Type*} [Fintype I] [DecidableEq I]

/-- The actual product of the output four-projector trace and the input Wick tensor trace. -/
def unchangedLocalContraction (u : Ω → sphere (0 : EuclideanSpace ℂ I) 1)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (x : Ω × (Ω × (Ω × Ω))) : ℂ :=
  Matrix.trace (vectorRankOne (u x.1).val (u x.1).val *
    vectorRankOne (u x.2.1).val (u x.2.1).val *
    vectorRankOne (u x.2.2.1).val (u x.2.2.1).val *
    vectorRankOne (u x.2.2.2).val (u x.2.2.2).val) *
  Matrix.trace (wickTensorMatrix (fun t : Fin 4 × Fin 2 =>
    vectorRankOne (u (fourRecordAt x t.1)).val (u (fourRecordAt x t.1)).val)*
    wickTensorPermutationMatrix π)

/-- The genuine matrix integrand is exactly the overlap product of the constructed six-regular graph. -/
theorem unchangedLocalContraction_norm
    (u : Ω → sphere (0 : EuclideanSpace ℂ I) 1)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π ∈ fourBlockDerangements)
    (x : Ω × (Ω × (Ω × Ω))) :
    ‖unchangedLocalContraction u π x‖=(wickFourVertexGraph π).overlapProduct u x := by
  unfold unchangedLocalContraction
  rw [norm_mul,vectorRankOne_four_trace,vectorRankOne_wick_trace_norm]
  simp only [norm_mul]
  have h := wickFourVertexGraph_product π hπ
    (fun i j => ‖inner ℂ (u (fourRecordAt x i)).val (u (fourRecordAt x j)).val‖)
    (fun i j => norm_inner_symm _ _)
  simpa [fourRecordAt,FourVertexMultigraph.overlapProduct,recordOverlap] using h

@[fun_prop] theorem unchangedLocalContraction_continuous [TopologicalSpace Ω]
    (u : Ω → sphere (0 : EuclideanSpace ℂ I) 1) (hu : Continuous u)
    (π : Equiv.Perm (Fin 4 × Fin 2)) : Continuous (unchangedLocalContraction u π) := by
  unfold unchangedLocalContraction
  simp_rw [vectorRankOne_four_trace,vectorRankOne_wick_trace]
  fun_prop

/-- The local Haar integrand uses exactly the pre-existing recordedProjector matrices. -/
def haarUnchangedSiteIntegrand (d : ℕ) [NeZero d]
    (π : Equiv.Perm (Fin 4 × Fin 2))
    (x : (ComplexUnitary (Fin d) × Fin d) ×
      ((ComplexUnitary (Fin d) × Fin d) × ((ComplexUnitary (Fin d) × Fin d) ×
        (ComplexUnitary (Fin d) × Fin d)))) : ℂ :=
  Matrix.trace (recordedProjector d x.1*recordedProjector d x.2.1*
    recordedProjector d x.2.2.1*recordedProjector d x.2.2.2)*
  Matrix.trace (wickTensorMatrix (fun t : Fin 4 × Fin 2 =>
    recordedProjector d (fourRecordAt x t.1))*wickTensorPermutationMatrix π)

theorem haarUnchangedSiteIntegrand_eq (d : ℕ) [NeZero d]
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    haarUnchangedSiteIntegrand d π=unchangedLocalContraction (haarRecordedUnitVector d) π := by
  funext x
  simp only [haarUnchangedSiteIntegrand,unchangedLocalContraction,vectorRankOne_haarRecord]

theorem haarUnchangedSiteIntegrand_integrable (d : ℕ) [NeZero d]
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Integrable (haarUnchangedSiteIntegrand d π) (fourReadoutLaw (haarBasisRecords d)) := by
  let : BorelSpace (ComplexUnitary (Fin d) × Fin d) := inferInstance
  let : SecondCountableTopology (ComplexUnitary (Fin d) × Fin d) := inferInstance
  rw [haarUnchangedSiteIntegrand_eq]
  exact (unchangedLocalContraction_continuous _ (haarRecordedUnitVector_continuous d) π
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Every actual Haar unchanged-site matrix contraction is bounded by the proved explicit κ. -/
theorem haarUnchangedSiteContraction_le (d : ℕ) [NeZero d]
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π ∈ fourBlockDerangements) :
    ‖(d:ℂ)^4*∫ x,haarUnchangedSiteIntegrand d π x ∂fourReadoutLaw (haarBasisRecords d)‖≤haarLocalKappa d := by
  rw [norm_mul,norm_pow,Complex.norm_natCast,haarUnchangedSiteIntegrand_eq]
  calc
    _ ≤ (d:ℝ)^4*∫ x,‖unchangedLocalContraction (haarRecordedUnitVector d) π x‖
        ∂fourReadoutLaw (haarBasisRecords d) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = (d:ℝ)^4*haarFourOverlapIntegral d (wickFourVertexGraph π) := by
      simp only [unchangedLocalContraction_norm _ π hπ,haarFourOverlapIntegral]
    _ ≤ _ := haarFourOverlapIntegral_scaled_le_via_incident_holder d _ (wickFourVertexGraph_regular π hπ)

/-- The rank-one matrix agrees with the full-record Pauli projector. -/
theorem vectorRankOne_pauliRecord (ω : PauliRecord) :
    vectorRankOne (pauliRecordedUnitVector ω).val (pauliRecordedUnitVector ω).val =
      pauliRecordedProjector ω := by
  ext i j
  exact (pauliRecordedProjector_apply ω i j).symm

def pauliUnchangedSiteIntegrand (π : Equiv.Perm (Fin 4 × Fin 2))
    (x : PauliRecord × (PauliRecord × (PauliRecord × PauliRecord))) : ℂ :=
  Matrix.trace (pauliRecordedProjector x.1*pauliRecordedProjector x.2.1*
    pauliRecordedProjector x.2.2.1*pauliRecordedProjector x.2.2.2)*
  Matrix.trace (wickTensorMatrix (fun t : Fin 4 × Fin 2 =>
    pauliRecordedProjector (fourRecordAt x t.1))*wickTensorPermutationMatrix π)

theorem pauliUnchangedSiteIntegrand_eq (π : Equiv.Perm (Fin 4 × Fin 2)) :
    pauliUnchangedSiteIntegrand π=unchangedLocalContraction pauliRecordedUnitVector π := by
  funext x
  simp only [pauliUnchangedSiteIntegrand,unchangedLocalContraction,vectorRankOne_pauliRecord]

theorem pauliUnchangedSiteIntegrand_integrable (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Integrable (pauliUnchangedSiteIntegrand π) (fourReadoutLaw pauliBasisRecords) := by
  rw [pauliUnchangedSiteIntegrand_eq]
  exact (unchangedLocalContraction_continuous _ pauliRecordedUnitVector_continuous π
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Every actual Pauli unchanged-site matrix contraction satisfies the strict local graph bound. -/
theorem pauliUnchangedSiteContraction_le (π : Equiv.Perm (Fin 4 × Fin 2))
    (hπ : π ∈ fourBlockDerangements) :
    ‖(16:ℂ)*∫ x,pauliUnchangedSiteIntegrand π x ∂fourReadoutLaw pauliBasisRecords‖≤pauliLocalKappa := by
  rw [norm_mul,Complex.norm_ofNat,pauliUnchangedSiteIntegrand_eq]
  calc
    _ ≤ 16*∫ x,‖unchangedLocalContraction pauliRecordedUnitVector π x‖
        ∂fourReadoutLaw pauliBasisRecords :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)
    _ = 16*pauliFourOverlapIntegral (wickFourVertexGraph π) := by
      simp only [unchangedLocalContraction_norm _ π hπ,pauliFourOverlapIntegral]
    _ ≤ _ := pauliFourOverlapIntegral_scaled_le_via_incident_holder _ (wickFourVertexGraph_regular π hπ)
      (wickFourVertexGraph_cycle π)

end CertificationGaussian
