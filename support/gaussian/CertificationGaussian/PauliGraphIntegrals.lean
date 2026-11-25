import CertificationGaussian.PauliBasisRecords

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian

theorem finite_readout_integrable {α : Type*} [Fintype α] [TopologicalSpace α]
    [DiscreteTopology α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) : Integrable f μ :=
  (show Continuous f from continuous_of_discreteTopology).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem pauliBasisRecords_integral_univ (f : PauliRecord → ℝ) :
    (∫ ω, f ω ∂pauliBasisRecords)=(1/6:ℝ)*∑ ω,f ω := by
  rw [pauliBasisRecords_integral,Fintype.sum_prod_type]

def pauliTripleLaw : Measure (PauliRecord × (PauliRecord × PauliRecord)) :=
  pauliBasisRecords.prod (pauliBasisRecords.prod pauliBasisRecords)

instance pauliTripleLaw_probability : IsProbabilityMeasure pauliTripleLaw := by
  unfold pauliTripleLaw
  infer_instance

theorem pauliTripleLaw_integral (f : PauliRecord × (PauliRecord × PauliRecord) → ℝ) :
    ∫ t,f t ∂pauliTripleLaw = ∫ b,∫ c,∫ d,f (b,c,d) ∂pauliBasisRecords ∂pauliBasisRecords ∂pauliBasisRecords := by
  rw [pauliTripleLaw,integral_prod _ (finite_readout_integrable _ f)]
  apply integral_congr_ae
  filter_upwards [] with b
  exact integral_prod _ (finite_readout_integrable _ _)

theorem pauliTripleLaw_integral_univ (f : PauliRecord × (PauliRecord × PauliRecord) → ℝ) :
    ∫ t,f t ∂pauliTripleLaw = (1/216:ℝ)*∑ t,f t := by
  rw [pauliTripleLaw_integral]
  simp_rw [pauliBasisRecords_integral_univ,← Finset.mul_sum]
  simp only [Fintype.sum_prod_type]
  ring

theorem pauli_integral_swap (f : PauliRecord → PauliRecord → ℝ) :
    (∫ a,∫ b,f a b ∂pauliBasisRecords ∂pauliBasisRecords) =
      ∫ b,∫ a,f a b ∂pauliBasisRecords ∂pauliBasisRecords :=
  integral_integral_swap (finite_readout_integrable _ _)

/-- Move the first record inside using true Fubini on the same four-copy probability. -/
theorem pauliFour_integral_first (f : PauliRecord × (PauliRecord × (PauliRecord × PauliRecord)) → ℝ) :
    ∫ x,f x ∂fourReadoutLaw pauliBasisRecords =
      ∫ t,∫ a,f (a,t.1,t.2.1,t.2.2) ∂pauliBasisRecords ∂pauliTripleLaw := by
  rw [fourReadoutLaw_integral pauliBasisRecords _ continuous_of_discreteTopology,
    pauliTripleLaw_integral,pauli_integral_swap]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [pauli_integral_swap]
  apply integral_congr_ae
  filter_upwards [] with c
  exact pauli_integral_swap _

def pauliIncidentProduct (g : FourVertexMultigraph)
    (t : PauliRecord × (PauliRecord × PauliRecord)) (s : PauliRecord) : ℝ :=
  recordOverlap pauliRecordedUnitVector s t.1^g.e01 *
    recordOverlap pauliRecordedUnitVector s t.2.1^g.e02 *
    recordOverlap pauliRecordedUnitVector s t.2.2^g.e03

def pauliConditionalIntegral (g : FourVertexMultigraph)
    (t : PauliRecord × (PauliRecord × PauliRecord)) : ℝ :=
  ∫ s,pauliIncidentProduct g t s ∂pauliBasisRecords

def pauliResidualProduct (g : FourVertexMultigraph)
    (t : PauliRecord × (PauliRecord × PauliRecord)) : ℝ :=
  recordOverlap pauliRecordedUnitVector t.1 t.2.1^g.e12 *
    recordOverlap pauliRecordedUnitVector t.1 t.2.2^g.e13 *
    recordOverlap pauliRecordedUnitVector t.2.1 t.2.2^g.e23

def pauliFourOverlapIntegral (g : FourVertexMultigraph) : ℝ :=
  ∫ x,g.overlapProduct pauliRecordedUnitVector x ∂fourReadoutLaw pauliBasisRecords

theorem pauliFourOverlapIntegral_conditional (g : FourVertexMultigraph) :
    pauliFourOverlapIntegral g =
      ∫ t,pauliResidualProduct g t*pauliConditionalIntegral g t ∂pauliTripleLaw := by
  rw [pauliFourOverlapIntegral,pauliFour_integral_first]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [pauliConditionalIntegral,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  unfold FourVertexMultigraph.overlapProduct pauliResidualProduct pauliIncidentProduct
  ring

theorem pauliResidualProduct_nonneg (g : FourVertexMultigraph)
    (t : PauliRecord × (PauliRecord × PauliRecord)) : 0≤pauliResidualProduct g t := by
  unfold pauliResidualProduct
  exact mul_nonneg (mul_nonneg (pow_nonneg (recordOverlap_nonneg _ _ _) _)
    (pow_nonneg (recordOverlap_nonneg _ _ _) _)) (pow_nonneg (recordOverlap_nonneg _ _ _) _)

/-- Conditional sixfold overlap is bounded by the actual Pauli moment 1/4. -/
theorem pauliConditionalIntegral_le (g : FourVertexMultigraph) (hg : g.IsSixRegular)
    (t : PauliRecord × (PauliRecord × PauliRecord)) : pauliConditionalIntegral g t≤(1/4:ℝ) := by
  have h := integral_mono (finite_readout_integrable pauliBasisRecords (pauliIncidentProduct g t))
    (finite_readout_integrable pauliBasisRecords (fun s =>
      ((g.e01:ℝ)*recordOverlap pauliRecordedUnitVector s t.1^6+
       (g.e02:ℝ)*recordOverlap pauliRecordedUnitVector s t.2.1^6+
       (g.e03:ℝ)*recordOverlap pauliRecordedUnitVector s t.2.2^6)/6))
    (fun s => three_matching_sixth_bound g.e01 g.e02 g.e03 hg.1 _ _ _
      (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _))
  rw [integral_div,integral_add (finite_readout_integrable _ _) (finite_readout_integrable _ _),
    integral_add (finite_readout_integrable _ _) (finite_readout_integrable _ _)] at h
  have hm (a : PauliRecord) :
      (∫ s,recordOverlap pauliRecordedUnitVector s a^6 ∂pauliBasisRecords)=(1/4:ℝ) := by
    calc
      _ = ∫ s,recordOverlap pauliRecordedUnitVector a s^6 ∂pauliBasisRecords :=
        integral_congr_ae (Filter.Eventually.of_forall (fun s =>
          congrArg (fun x : ℝ => x^6) (recordOverlap_symm _ s a)))
      _ = _ := pauliBasisRecords_overlap_sixth a
  simp_rw [integral_const_mul,hm] at h
  change pauliConditionalIntegral g t≤_ at h
  have hs : (g.e01:ℝ)+g.e02+g.e03=6 := by exact_mod_cast hg.1
  linarith

/-- Each remaining edge has the same sixth moment under the actual triple product law. -/
theorem pauliTriple_edge_sixth :
    (∫ t,recordOverlap pauliRecordedUnitVector t.1 t.2.1^6 ∂pauliTripleLaw)=(1/4:ℝ) ∧
    (∫ t,recordOverlap pauliRecordedUnitVector t.1 t.2.2^6 ∂pauliTripleLaw)=(1/4:ℝ) ∧
    (∫ t,recordOverlap pauliRecordedUnitVector t.2.1 t.2.2^6 ∂pauliTripleLaw)=(1/4:ℝ) := by
  simp_rw [pauliTripleLaw_integral]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,pauliBasisRecords_overlap_sixth]
  norm_num

theorem pauliResidualProduct_integral_le (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    (∫ t,pauliResidualProduct g t ∂pauliTripleLaw)≤(1/4:ℝ) := by
  have hsum : g.e12+g.e13+g.e23=6 := by
    obtain ⟨h1,h2,h3⟩ := g.opposite_eq hg
    have hg0 := hg.1
    omega
  have h := integral_mono (finite_readout_integrable pauliTripleLaw (pauliResidualProduct g))
    (finite_readout_integrable pauliTripleLaw (fun t =>
      ((g.e12:ℝ)*recordOverlap pauliRecordedUnitVector t.1 t.2.1^6+
       (g.e13:ℝ)*recordOverlap pauliRecordedUnitVector t.1 t.2.2^6+
       (g.e23:ℝ)*recordOverlap pauliRecordedUnitVector t.2.1 t.2.2^6)/6))
    (fun t => three_matching_sixth_bound g.e12 g.e13 g.e23 hsum _ _ _
      (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _))
  rw [integral_div,integral_add (finite_readout_integrable _ _) (finite_readout_integrable _ _),
    integral_add (finite_readout_integrable _ _) (finite_readout_integrable _ _)] at h
  simp_rw [integral_const_mul,pauliTriple_edge_sixth.1,pauliTriple_edge_sixth.2.1,
    pauliTriple_edge_sixth.2.2] at h
  have hs : (g.e12:ℝ)+g.e13+g.e23=6 := by exact_mod_cast hsum
  linarith

end CertificationGaussian
