import CertificationGaussian.IncidentHolderContractions
import CertificationGaussian.CompleteMUBGraphKappa
import CertificationGaussian.ChangedSiteContraction
import CertificationGaussian.ReadoutChoiLocal

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace CertificationGaussian
variable {d : ℕ} [NeZero d] (B : CompleteMUB d)

/-- The actual MUB changed-site tensor under the same complete record law. -/
def completeMUBChangedSiteTensor (a b : Bool) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  (d:ℝ) • ∫ ω,localChangedSiteIntegrand d a b (completeMUBFullRecord B ω)∂completeMUBRecords d

theorem completeMUBChangedSite_integrand_integrable (a b : Bool) :
    Integrable (fun ω => localChangedSiteIntegrand d a b (completeMUBFullRecord B ω))
      (completeMUBRecords d) :=
  (show Continuous (fun ω => localChangedSiteIntegrand d a b (completeMUBFullRecord B ω)) from
    continuous_of_discreteTopology).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

omit [NeZero d] in
theorem completeMUBChangedSiteTensor_posSemidef (a b : Bool) :
    (completeMUBChangedSiteTensor B a b).PosSemidef := by
  unfold completeMUBChangedSiteTensor
  apply Matrix.PosSemidef.smul _ (Nat.cast_nonneg d)
  exact (integral_nonneg (fun ω =>
    (localChangedSiteIntegrand_posSemidef d a b (completeMUBFullRecord B ω)).nonneg)).posSemidef

theorem completeMUBChangedSiteTensor_trace (a b : Bool) :
    Matrix.trace (completeMUBChangedSiteTensor B a b)=
      (d:ℂ)*(if a then (d:ℂ)-1 else 1)*(if b then (d:ℂ)-1 else 1) := by
  let L := (Matrix.traceLinearMap ((Fin d × Fin d) × Fin d) ℝ ℂ).toContinuousLinearMap
  have h := L.integral_comp_comm (completeMUBChangedSite_integrand_integrable B a b)
  change (∫ ω,Matrix.trace (localChangedSiteIntegrand d a b (completeMUBFullRecord B ω))
      ∂completeMUBRecords d)=
    Matrix.trace (∫ ω,localChangedSiteIntegrand d a b (completeMUBFullRecord B ω)
      ∂completeMUBRecords d) at h
  rw [completeMUBChangedSiteTensor,Matrix.trace_smul,← h]
  simp [localChangedSiteIntegrand_trace,Complex.real_smul]
  ring_nf

theorem completeMUBChangedSiteTensor_trace_power (a b : Bool) :
    Matrix.trace (completeMUBChangedSiteTensor B a b)=(d:ℂ)*((d:ℂ)-1)^(a.toNat+b.toNat) := by
  rw [completeMUBChangedSiteTensor_trace]
  cases a <;> cases b <;> simp [pow_two,mul_assoc]

theorem completeMUBChangedSiteTensor_trace_le (hd : 2≤d) (a b : Bool) :
    (Matrix.trace (completeMUBChangedSiteTensor B a b)).re≤(d:ℝ)*((d:ℝ)-1)^2 := by
  rw [completeMUBChangedSiteTensor_trace,← haarChangedSiteTensor_trace d a b]
  exact haarChangedSiteTensor_trace_le d hd a b

theorem completeMUBChangedSite_four_unitary_bound (hd : 2≤d) (a b : Fin 4 → Bool)
    (U : Matrix (Fin 4 → ((Fin d × Fin d) × Fin d)) (Fin 4 → ((Fin d × Fin d) × Fin d)) ℂ)
    (hU : U∈unitary _) :
    ‖Matrix.trace (wickTensorMatrix (fun v => completeMUBChangedSiteTensor B (a v) (b v))*U)‖≤
      (d:ℝ)^4*((d:ℝ)-1)^8 := by
  let K := fun v : Fin 4 => completeMUBChangedSiteTensor B (a v) (b v)
  have hK : ∀ v,(K v).PosSemidef := fun v => completeMUBChangedSiteTensor_posSemidef B (a v) (b v)
  calc
    _ ≤ (Matrix.trace (wickTensorMatrix K)).re :=
      posSemidef_trace_unitary_le _ _ (wickTensorMatrix_posSemidef K hK) hU
    _ = ∏ v,(Matrix.trace (K v)).re := wickTensorMatrix_trace_re K hK
    _ ≤ ∏ _v : Fin 4,(d:ℝ)*((d:ℝ)-1)^2 := Finset.prod_le_prod₀
      (fun v _ => (RCLike.nonneg_iff.mp (hK v).trace_nonneg).1)
      (fun v _ => completeMUBChangedSiteTensor_trace_le B hd (a v) (b v))
    _ = _ := by simp; ring_nf

/-- Actual full-record unchanged-site matrices, retaining their complex phases. -/
def completeMUBUnchangedSiteIntegrand (π : Equiv.Perm (Fin 4 × Fin 2))
    (x : CompleteMUBRecord d × (CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d))) : ℂ :=
  Matrix.trace (completeMUBProjector B x.1*completeMUBProjector B x.2.1*
    completeMUBProjector B x.2.2.1*completeMUBProjector B x.2.2.2)*
  Matrix.trace (wickTensorMatrix (fun t : Fin 4 × Fin 2 =>
    completeMUBProjector B (fourRecordAt x t.1))*wickTensorPermutationMatrix π)

theorem completeMUBUnchangedSiteIntegrand_eq (π : Equiv.Perm (Fin 4 × Fin 2)) :
    completeMUBUnchangedSiteIntegrand B π=unchangedLocalContraction (completeMUBUnitVector B) π := by
  funext x
  simp only [completeMUBUnchangedSiteIntegrand,unchangedLocalContraction,
    completeMUB_projector_eq_rankOne]

theorem completeMUBUnchangedSiteContraction_le (hd : 2≤d)
    (π : Equiv.Perm (Fin 4 × Fin 2)) (hπ : π∈fourBlockDerangements) :
    ‖(d:ℂ)^4*∫ x,completeMUBUnchangedSiteIntegrand B π x∂fourReadoutLaw (completeMUBRecords d)‖≤
      completeMUBLocalKappa d := by
  rw [norm_mul,norm_pow,Complex.norm_natCast,completeMUBUnchangedSiteIntegrand_eq]
  calc
    _ ≤ (d:ℝ)^4*∫ x,‖unchangedLocalContraction (completeMUBUnitVector B) π x‖
        ∂fourReadoutLaw (completeMUBRecords d) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = (d:ℝ)^4*completeMUBFourOverlapIntegral B (wickFourVertexGraph π) := by
      simp only [unchangedLocalContraction_norm _ π hπ,completeMUBFourOverlapIntegral]
    _ ≤ _ := completeMUBFourOverlapIntegral_scaled_le_via_incident_holder B hd _ (wickFourVertexGraph_regular π hπ)
      (wickFourVertexGraph_cycle π)

theorem completeMUBChangedSiteIntegral_eq_tensor (a : Fin 4 × Fin 2 → Bool)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    (d:ℂ)^4*(∫ x,recordedChangedSiteIntegrand d (completeMUBFullRecord B) a π x
      ∂fourReadoutLaw (completeMUBRecords d))=
      Matrix.trace (wickTensorMatrix (fun b : Fin 4 => completeMUBChangedSiteTensor B (a (b,0)) (a (b,1)))*
        combinedWickPermutationMatrix π) :=
  recordedChangedSiteIntegral_eq_tensor (completeMUBRecords d) d (completeMUBFullRecord B)
    continuous_of_discreteTopology a π

theorem completeMUBChangedSiteContraction_le (hd : 2≤d) (a : Fin 4 × Fin 2 → Bool)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    ‖(d:ℂ)^4*(∫ x,recordedChangedSiteIntegrand d (completeMUBFullRecord B) a π x
      ∂fourReadoutLaw (completeMUBRecords d))‖≤(d:ℝ)^4*((d:ℝ)-1)^8 := by
  rw [completeMUBChangedSiteIntegral_eq_tensor]
  exact completeMUBChangedSite_four_unitary_bound B hd (fun b => a (b,0)) (fun b => a (b,1))
    _ (combinedWickPermutationMatrix_unitary π)

/-- Both actual local Choi factors are supplied by the proved finite MUB twirls. -/
theorem completeMUBRecords_choi_entries (i a j b : Fin d) :
    ((d:ℂ)*(∫ ω,completeMUBProjector B ω a b*completeMUBProjector B ω j i∂completeMUBRecords d)=
      radialChoiA0 d (i,a) (j,b)) ∧
    ((d:ℂ)*(∫ ω,completeMUBProjector B ω a b*(1-completeMUBProjector B ω) j i∂completeMUBRecords d)=
      (d:ℂ)*radialChoiR0 d (i,a) (j,b)) :=
  ⟨localReadoutChoi_success d (NeZero.pos d) (completeMUBRecords d) (completeMUBFullRecord B)
      (completeMUBRecords_success B) i a j b,
    localReadoutChoi_complement d (completeMUBRecords d) (completeMUBFullRecord B)
      (completeMUBRecords_complement B) i a j b⟩

end CertificationGaussian
