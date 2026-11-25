import CertificationGaussian.PauliGraphKappa
import CertificationGaussian.PauliChangedSiteTensor
import CertificationGaussian.Consumers.HaarGraphKappa

noncomputable section
open MeasureTheory Metric Set Matrix
open scoped BigOperators ENNReal MatrixOrder ComplexOrder
namespace CertificationGaussian.Consumers

/-- Actual finite Z/X/Y readout supplies one strict constant for all allowed local graphs. -/
theorem actual_pauli_graph_contraction :
    0<pauliLocalKappa ∧ pauliLocalKappa<1 ∧ ∀ g : FourVertexMultigraph,
      g.IsSixRegular → g.ContainsFourCycle → 16*pauliFourOverlapIntegral g≤pauliLocalKappa :=
  pauli_local_graph_contraction

theorem pauli_kappa_explicit :
    pauliLocalKappa=1-(5/2592:ℝ)*(1-(Real.sqrt 2)⁻¹) := by
  unfold pauliLocalKappa pauliStrictLoss
  ring

/-- Each complete finite basis/outcome record has mass exactly 1/6. -/
theorem pauli_record_mass (ω : PauliRecord) : pauliBasisRecords {ω}=(1/6:ℝ≥0∞) := by
  obtain ⟨b,j⟩ := ω
  rw [pauliBasisRecords,← Set.singleton_prod_singleton,Measure.prod_prod]
  norm_num [uniformFiniteOutcome,Measure.smul_apply]
  rw [← ENNReal.mul_inv (a := 3) (b := 2) (by norm_num) (by norm_num)]
  norm_num

/-- The concrete strict-loss event uses three complete records and has positive mass 1/216. -/
theorem pauli_strict_event_mass : pauliTripleLaw {pauliStrictTriple}=(1/216:ℝ≥0∞) := by
  have hpair : (pauliBasisRecords.prod pauliBasisRecords) {(pauliRecordE,pauliRecordF)} =
      pauliBasisRecords {pauliRecordE}*pauliBasisRecords {pauliRecordF} := by
    rw [← Set.singleton_prod_singleton,Measure.prod_prod]
  rw [pauliTripleLaw,pauliStrictTriple,← Set.singleton_prod_singleton,Measure.prod_prod,hpair]
  simp only [pauli_record_mass,one_div]
  rw [← ENNReal.mul_inv (a := 6) (b := 6) (by norm_num) (by norm_num)]
  norm_num
  rw [← ENNReal.mul_inv (a := 6) (b := 36) (by norm_num) (by norm_num)]
  norm_num

/-- A genuine mixed-multiplicity four-cycle consumes the strict Pauli result. -/
theorem pauli_mixed_graph_strict :
    16*pauliFourOverlapIntegral mixedSixGraph≤pauliLocalKappa ∧ pauliLocalKappa<1 :=
  ⟨pauliFourOverlapIntegral_scaled_le mixedSixGraph mixedSixGraph_regular_cycle.1
    mixedSixGraph_regular_cycle.2,pauliLocalKappa_lt_one⟩

/-- Without the four-cycle hypothesis the non-strict bound is sharp; the hypothesis is material. -/
theorem pauli_disconnected_graph_exact : pauliFourOverlapIntegral disconnectedSixGraph=(1/16:ℝ) := by
  unfold pauliFourOverlapIntegral
  simp_rw [disconnectedSixGraph.overlapProduct_matchings
    pauliRecordedUnitVector disconnectedSixGraph_regular]
  simp only [disconnectedSixGraph,pow_zero,mul_one]
  have h := matchingOverlap01_sixth pauliBasisRecords pauliRecordedUnitVector
    pauliRecordedUnitVector_continuous (1/4:ℝ) pauliBasisRecords_overlap_sixth
  norm_num at h
  exact h

theorem pauli_disconnected_fails_strict :
    ¬16*pauliFourOverlapIntegral disconnectedSixGraph≤pauliLocalKappa := by
  rw [pauli_disconnected_graph_exact]
  linarith [pauliLocalKappa_lt_one]

/-- The exact same reference records support both success and complement twirls, for all complex A. -/
theorem pauli_actual_twirls (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ((2:ℂ)*∫ ω,pauliRecordedProjector ω i j*Matrix.trace (pauliRecordedProjector ω*A)
      ∂pauliBasisRecords = (A i j + if i=j then Matrix.trace A else 0)/3) ∧
    ((2:ℂ)*∫ ω,pauliRecordedProjector ω i j*Matrix.trace ((1-pauliRecordedProjector ω)*A)
      ∂pauliBasisRecords = ((if i=j then 2*Matrix.trace A else 0)-A i j)/3) :=
  ⟨pauliBasisRecords_success A i j,pauliBasisRecords_complement A i j⟩

/-- Nilpotent off-diagonal data confirms that the local twirls impose no Hermitian premise. -/
theorem pauli_nilpotent_twirls :
    ((2:ℂ)*∫ ω,pauliRecordedProjector ω 0 1*Matrix.trace
      (pauliRecordedProjector ω* (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℂ))
      ∂pauliBasisRecords = 1/3) ∧
    ((2:ℂ)*∫ ω,pauliRecordedProjector ω 0 1*Matrix.trace
      ((1-pauliRecordedProjector ω)*(!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℂ))
      ∂pauliBasisRecords = -1/3) := by
  simpa using pauli_actual_twirls (!![0,1;0,0]) 0 1

/-- Same-record changed-site tensors are actual positive Bochner averages with trace two. -/
theorem pauli_actual_changed_site (a b : Bool) :
    (pauliChangedSiteTensor a b).PosSemidef ∧ Matrix.trace (pauliChangedSiteTensor a b)=2 :=
  ⟨pauliChangedSiteTensor_posSemidef a b,pauliChangedSiteTensor_trace a b⟩

theorem pauli_actual_changed_site_cost (a b : Fin 4 → Bool)
    (U : Matrix (Fin 4 → ((Fin 2 × Fin 2) × Fin 2)) (Fin 4 → ((Fin 2 × Fin 2) × Fin 2)) ℂ)
    (hU : U ∈ unitary _) :
    ‖Matrix.trace (wickTensorMatrix (fun v => pauliChangedSiteTensor (a v) (b v))*U)‖≤16 :=
  pauliChangedSite_four_unitary_bound a b U hU

end CertificationGaussian.Consumers
