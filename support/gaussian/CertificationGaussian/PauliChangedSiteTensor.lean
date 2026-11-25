import CertificationGaussian.PauliTwirl

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace CertificationGaussian

/-- The actual changed-site Pauli tensor, integrated over full finite basis/outcome records. -/
def pauliChangedSiteTensor (a b : Bool) :
    Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  (2:ℝ) • ∫ ω,localChangedSiteIntegrand 2 a b (pauliFullRecord ω) ∂pauliBasisRecords

theorem pauliChangedSite_integrand_integrable (a b : Bool) :
    Integrable (fun ω => localChangedSiteIntegrand 2 a b (pauliFullRecord ω)) pauliBasisRecords :=
  (show Continuous (fun ω => localChangedSiteIntegrand 2 a b (pauliFullRecord ω)) from
    continuous_of_discreteTopology).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem pauliChangedSiteTensor_posSemidef (a b : Bool) :
    (pauliChangedSiteTensor a b).PosSemidef := by
  unfold pauliChangedSiteTensor
  apply Matrix.PosSemidef.smul _ (by norm_num)
  exact (integral_nonneg (fun ω =>
    (localChangedSiteIntegrand_posSemidef 2 a b (pauliFullRecord ω)).nonneg)).posSemidef

/-- For d=2, all four choices P or I-P have exact trace two. -/
theorem pauliChangedSiteTensor_trace (a b : Bool) : Matrix.trace (pauliChangedSiteTensor a b)=(2:ℂ) := by
  let L := (Matrix.traceLinearMap ((Fin 2 × Fin 2) × Fin 2) ℝ ℂ).toContinuousLinearMap
  have h := L.integral_comp_comm (pauliChangedSite_integrand_integrable a b)
  change (∫ ω,Matrix.trace (localChangedSiteIntegrand 2 a b (pauliFullRecord ω)) ∂pauliBasisRecords)=
    Matrix.trace (∫ ω,localChangedSiteIntegrand 2 a b (pauliFullRecord ω) ∂pauliBasisRecords) at h
  rw [pauliChangedSiteTensor,Matrix.trace_smul,← h]
  norm_num [localChangedSiteIntegrand_trace,Complex.real_smul]

/-- The actual four-block Pauli changed-site cost is C2=16 for every genuine unitary contraction. -/
theorem pauliChangedSite_four_unitary_bound (a b : Fin 4 → Bool)
    (U : Matrix (Fin 4 → ((Fin 2 × Fin 2) × Fin 2)) (Fin 4 → ((Fin 2 × Fin 2) × Fin 2)) ℂ)
    (hU : U ∈ unitary _) :
    ‖Matrix.trace (wickTensorMatrix (fun v => pauliChangedSiteTensor (a v) (b v))*U)‖≤16 := by
  have hK (v : Fin 4) := pauliChangedSiteTensor_posSemidef (a v) (b v)
  have h := posSemidef_trace_unitary_le _ U
    (wickTensorMatrix_posSemidef (fun v => pauliChangedSiteTensor (a v) (b v)) hK) hU
  rw [wickTensorMatrix_trace_re _ hK] at h
  norm_num [pauliChangedSiteTensor_trace] at h
  exact h

end CertificationGaussian
