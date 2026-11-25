import CertificationGaussian.CompleteMUBTwirl

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian
variable {d : ℕ} [NeZero d]

theorem completeMUBRecords_integral_univ (f : CompleteMUBRecord d → ℝ) :
    (∫ ω,f ω∂completeMUBRecords d)=((d+1:ℝ)*(d:ℝ))⁻¹*∑ ω,f ω := by
  rw [completeMUBRecords_integral,Fintype.sum_prod_type]

def completeMUBTripleLaw (d : ℕ) : Measure (CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d)) :=
  (completeMUBRecords d).prod ((completeMUBRecords d).prod (completeMUBRecords d))

instance completeMUBTripleLaw_probability : IsProbabilityMeasure (completeMUBTripleLaw d) := by
  unfold completeMUBTripleLaw
  infer_instance

theorem completeMUBTripleLaw_integral
    (f : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d) → ℝ) :
    ∫ t,f t∂completeMUBTripleLaw d=
      ∫ b,∫ c,∫ e,f (b,c,e)∂completeMUBRecords d∂completeMUBRecords d∂completeMUBRecords d := by
  rw [completeMUBTripleLaw,integral_prod _ (finite_readout_integrable _ f)]
  apply integral_congr_ae
  filter_upwards [] with b
  exact integral_prod _ (finite_readout_integrable _ _)

theorem completeMUBTripleLaw_integral_univ
    (f : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d) → ℝ) :
    ∫ t,f t∂completeMUBTripleLaw d=(((d+1:ℝ)*(d:ℝ))⁻¹)^3*∑ t,f t := by
  rw [completeMUBTripleLaw_integral]
  simp_rw [completeMUBRecords_integral_univ,← Finset.mul_sum]
  simp only [Fintype.sum_prod_type]
  ring

theorem completeMUB_integral_swap (f : CompleteMUBRecord d → CompleteMUBRecord d → ℝ) :
    (∫ a,∫ b,f a b∂completeMUBRecords d∂completeMUBRecords d)=
      ∫ b,∫ a,f a b∂completeMUBRecords d∂completeMUBRecords d :=
  integral_integral_swap (finite_readout_integrable _ _)

theorem completeMUBFour_integral_first
    (f : CompleteMUBRecord d × (CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d)) → ℝ) :
    ∫ x,f x∂fourReadoutLaw (completeMUBRecords d)=
      ∫ t,∫ a,f (a,t.1,t.2.1,t.2.2)∂completeMUBRecords d∂completeMUBTripleLaw d := by
  rw [fourReadoutLaw_integral (completeMUBRecords d) _ continuous_of_discreteTopology,
    completeMUBTripleLaw_integral,completeMUB_integral_swap]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [completeMUB_integral_swap]
  apply integral_congr_ae
  filter_upwards [] with c
  exact completeMUB_integral_swap _

variable (B : CompleteMUB d)

def completeMUBIncidentProduct (g : FourVertexMultigraph)
    (t : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d))
    (s : CompleteMUBRecord d) : ℝ :=
  recordOverlap (completeMUBUnitVector B) s t.1^g.e01 *
    recordOverlap (completeMUBUnitVector B) s t.2.1^g.e02 *
    recordOverlap (completeMUBUnitVector B) s t.2.2^g.e03

def completeMUBConditionalIntegral (g : FourVertexMultigraph)
    (t : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d)) : ℝ :=
  ∫ s,completeMUBIncidentProduct B g t s∂completeMUBRecords d

def completeMUBResidualProduct (g : FourVertexMultigraph)
    (t : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d)) : ℝ :=
  recordOverlap (completeMUBUnitVector B) t.1 t.2.1^g.e12 *
    recordOverlap (completeMUBUnitVector B) t.1 t.2.2^g.e13 *
    recordOverlap (completeMUBUnitVector B) t.2.1 t.2.2^g.e23

def completeMUBFourOverlapIntegral (g : FourVertexMultigraph) : ℝ :=
  ∫ x,g.overlapProduct (completeMUBUnitVector B) x∂fourReadoutLaw (completeMUBRecords d)

theorem completeMUBFourOverlapIntegral_conditional (g : FourVertexMultigraph) :
    completeMUBFourOverlapIntegral B g=
      ∫ t,completeMUBResidualProduct B g t*completeMUBConditionalIntegral B g t∂completeMUBTripleLaw d := by
  rw [completeMUBFourOverlapIntegral,completeMUBFour_integral_first]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [completeMUBConditionalIntegral,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  unfold FourVertexMultigraph.overlapProduct completeMUBResidualProduct completeMUBIncidentProduct
  ring

theorem completeMUBResidualProduct_nonneg (g : FourVertexMultigraph)
    (t : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d)) :
    0≤completeMUBResidualProduct B g t := by
  unfold completeMUBResidualProduct
  exact mul_nonneg (mul_nonneg (pow_nonneg (recordOverlap_nonneg _ _ _) _)
    (pow_nonneg (recordOverlap_nonneg _ _ _) _)) (pow_nonneg (recordOverlap_nonneg _ _ _) _)

theorem completeMUBConditionalIntegral_le (g : FourVertexMultigraph) (hg : g.IsSixRegular)
    (t : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d)) :
    completeMUBConditionalIntegral B g t≤((d:ℝ)⁻¹)^2 := by
  have h := integral_mono (finite_readout_integrable (completeMUBRecords d) (completeMUBIncidentProduct B g t))
    (finite_readout_integrable (completeMUBRecords d) (fun s =>
      ((g.e01:ℝ)*recordOverlap (completeMUBUnitVector B) s t.1^6+
       (g.e02:ℝ)*recordOverlap (completeMUBUnitVector B) s t.2.1^6+
       (g.e03:ℝ)*recordOverlap (completeMUBUnitVector B) s t.2.2^6)/6))
    (fun s => three_matching_sixth_bound g.e01 g.e02 g.e03 hg.1 _ _ _
      (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _))
  rw [integral_div,integral_add (finite_readout_integrable _ _) (finite_readout_integrable _ _),
    integral_add (finite_readout_integrable _ _) (finite_readout_integrable _ _)] at h
  have hm (a : CompleteMUBRecord d) :
      (∫ s,recordOverlap (completeMUBUnitVector B) s a^6∂completeMUBRecords d)=((d:ℝ)⁻¹)^2 := by
    calc
      _ = ∫ s,recordOverlap (completeMUBUnitVector B) a s^6∂completeMUBRecords d :=
        integral_congr_ae (Filter.Eventually.of_forall (fun s =>
          congrArg (fun x : ℝ => x^6) (recordOverlap_symm _ s a)))
      _ = _ := completeMUBRecords_overlap_sixth B a
  simp_rw [integral_const_mul,hm] at h
  change completeMUBConditionalIntegral B g t≤_ at h
  have hs : (g.e01:ℝ)+g.e02+g.e03=6 := by exact_mod_cast hg.1
  nlinarith [sq_nonneg ((d:ℝ)⁻¹)]

theorem completeMUBTriple_edge_sixth :
    (∫ t,recordOverlap (completeMUBUnitVector B) t.1 t.2.1^6∂completeMUBTripleLaw d)=((d:ℝ)⁻¹)^2 ∧
    (∫ t,recordOverlap (completeMUBUnitVector B) t.1 t.2.2^6∂completeMUBTripleLaw d)=((d:ℝ)⁻¹)^2 ∧
    (∫ t,recordOverlap (completeMUBUnitVector B) t.2.1 t.2.2^6∂completeMUBTripleLaw d)=((d:ℝ)⁻¹)^2 := by
  simp_rw [completeMUBTripleLaw_integral]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,completeMUBRecords_overlap_sixth]
  trivial

theorem completeMUBResidualProduct_integral_le (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    (∫ t,completeMUBResidualProduct B g t∂completeMUBTripleLaw d)≤((d:ℝ)⁻¹)^2 := by
  have hsum : g.e12+g.e13+g.e23=6 := by
    obtain ⟨h1,h2,h3⟩ := g.opposite_eq hg
    have hg0 := hg.1
    omega
  have h := integral_mono (finite_readout_integrable (completeMUBTripleLaw d) (completeMUBResidualProduct B g))
    (finite_readout_integrable (completeMUBTripleLaw d) (fun t =>
      ((g.e12:ℝ)*recordOverlap (completeMUBUnitVector B) t.1 t.2.1^6+
       (g.e13:ℝ)*recordOverlap (completeMUBUnitVector B) t.1 t.2.2^6+
       (g.e23:ℝ)*recordOverlap (completeMUBUnitVector B) t.2.1 t.2.2^6)/6))
    (fun t => three_matching_sixth_bound g.e12 g.e13 g.e23 hsum _ _ _
      (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _) (recordOverlap_nonneg _ _ _))
  rw [integral_div,integral_add (finite_readout_integrable _ _) (finite_readout_integrable _ _),
    integral_add (finite_readout_integrable _ _) (finite_readout_integrable _ _)] at h
  simp_rw [integral_const_mul,(completeMUBTriple_edge_sixth B).1,(completeMUBTriple_edge_sixth B).2.1,
    (completeMUBTriple_edge_sixth B).2.2] at h
  have hs : (g.e12:ℝ)+g.e13+g.e23=6 := by exact_mod_cast hsum
  nlinarith [sq_nonneg ((d:ℝ)⁻¹)]

end CertificationGaussian
