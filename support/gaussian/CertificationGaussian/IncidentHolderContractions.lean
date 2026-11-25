import CertificationGaussian.IncidentOverlapHolder
import CertificationGaussian.HaarGraphKappa
import CertificationGaussian.PauliGraphKappa
import CertificationGaussian.CompleteMUBGraphKappa

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian

/-- Actual Haar-record contraction via padded incident Hölder and vertex elimination. -/
theorem haarFourOverlapIntegral_le_via_incident_holder (d : ℕ) [NeZero d]
    (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    haarFourOverlapIntegral d g ≤ (6/((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2)))^2 := by
  exact IncidentHolder.overlap_integral_le (haarBasisRecords d) (haarRecordedUnitVector d) g hg
    (haarRecordedUnitVector_continuous d) _ (by positivity)
    (fun a => haarBasisRecords_overlap_sixth d _)

theorem haarFourOverlapIntegral_scaled_le_via_incident_holder (d : ℕ) [NeZero d]
    (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    (d:ℝ)^4*haarFourOverlapIntegral d g ≤ haarLocalKappa d := by
  have h := mul_le_mul_of_nonneg_left (haarFourOverlapIntegral_le_via_incident_holder d g hg)
    (show (0:ℝ)≤(d:ℝ)^4 by positivity)
  have he : (d:ℝ)^4*(6/((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2)))^2 = haarLocalKappa d := by
    have hd : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
    unfold haarLocalKappa
    field_simp
    ring
  exact h.trans_eq he

theorem haar_local_graph_contraction_via_incident_holder (d : ℕ) [NeZero d] (hd : 3≤d) :
    0<haarLocalKappa d ∧ haarLocalKappa d<1 ∧
      ∀ (g : FourVertexMultigraph), g.IsSixRegular →
        (d:ℝ)^4*haarFourOverlapIntegral d g ≤ haarLocalKappa d :=
  ⟨haarLocalKappa_pos d (by omega),haarLocalKappa_lt_one d hd,
    fun g hg => haarFourOverlapIntegral_scaled_le_via_incident_holder d g hg⟩

/-- The first Pauli vertex is estimated by six incident factors. -/
theorem pauliConditionalIntegral_le_via_incident_holder (g : FourVertexMultigraph) (hg : g.IsSixRegular)
    (t : PauliRecord × (PauliRecord × PauliRecord)) : pauliConditionalIntegral g t≤(1/4:ℝ) := by
  have h := IncidentHolder.incident_overlap_holder_left pauliBasisRecords pauliRecordedUnitVector
    (show Continuous pauliRecordedUnitVector from continuous_of_discreteTopology)
    (1/4) pauliBasisRecords_overlap_sixth g.e01 g.e02 g.e03 hg.1.le t.1 t.2.1 t.2.2
  simpa only [pauliConditionalIntegral,pauliIncidentProduct,hg.1,IncidentHolder.sixthRoot_pow_six (1/4) (by norm_num)] using h

/-- The six residual Pauli edges are estimated by eliminating two further vertices. -/
theorem pauliResidualProduct_integral_le_via_incident_holder (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    (∫ t,pauliResidualProduct g t ∂pauliTripleLaw)≤(1/4:ℝ) := by
  have hs : g.e12+g.e13+g.e23=6 := by obtain ⟨h0,h1,h2,h3⟩ := hg; omega
  have ha : g.e12≤6 := by have := hg.2.1; omega
  have hbc : g.e13+g.e23≤6 := by have := hg.2.2.2; omega
  rw [pauliTripleLaw_integral]
  have h := IncidentHolder.triangle_elimination pauliBasisRecords pauliRecordedUnitVector
    (show Continuous pauliRecordedUnitVector from continuous_of_discreteTopology)
    (1/4) (by norm_num) pauliBasisRecords_overlap_sixth g.e12 g.e13 g.e23 ha hbc
  simpa only [pauliResidualProduct,hs,IncidentHolder.sixthRoot_pow_six (1/4) (by norm_num)] using h

variable {d : ℕ} [NeZero d]

/-- Hölder applies to records of the supplied MUB; no existence or replacement law is assumed. -/
theorem completeMUBConditionalIntegral_le_via_incident_holder (B : CompleteMUB d)
    (g : FourVertexMultigraph) (hg : g.IsSixRegular)
    (t : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d)) :
    completeMUBConditionalIntegral B g t≤((d:ℝ)⁻¹)^2 := by
  have h := IncidentHolder.incident_overlap_holder_left (completeMUBRecords d) (completeMUBUnitVector B)
    (show Continuous (completeMUBUnitVector B) from continuous_of_discreteTopology)
    (((d:ℝ)⁻¹)^2) (completeMUBRecords_overlap_sixth B)
    g.e01 g.e02 g.e03 hg.1.le t.1 t.2.1 t.2.2
  simpa only [completeMUBConditionalIntegral,completeMUBIncidentProduct,hg.1,IncidentHolder.sixthRoot_pow_six _ (sq_nonneg ((d:ℝ)⁻¹))] using h

theorem completeMUBResidualProduct_integral_le_via_incident_holder (B : CompleteMUB d)
    (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    (∫ t,completeMUBResidualProduct B g t∂completeMUBTripleLaw d)≤((d:ℝ)⁻¹)^2 := by
  have hs : g.e12+g.e13+g.e23=6 := by obtain ⟨h0,h1,h2,h3⟩ := hg; omega
  have ha : g.e12≤6 := by have := hg.2.1; omega
  have hbc : g.e13+g.e23≤6 := by have := hg.2.2.2; omega
  rw [completeMUBTripleLaw_integral]
  have h := IncidentHolder.triangle_elimination (completeMUBRecords d) (completeMUBUnitVector B)
    (show Continuous (completeMUBUnitVector B) from continuous_of_discreteTopology)
    (((d:ℝ)⁻¹)^2) (sq_nonneg _) (completeMUBRecords_overlap_sixth B)
    g.e12 g.e13 g.e23 ha hbc
  simpa only [completeMUBResidualProduct,hs,IncidentHolder.sixthRoot_pow_six _ (sq_nonneg ((d:ℝ)⁻¹))] using h

/-- Strict graph loss for the six actual Pauli records, uniformly in all allowed multiplicities. -/
theorem pauliFourOverlapIntegral_strict_via_incident_holder (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    pauliFourOverlapIntegral g≤(1/16:ℝ)-pauliStrictLoss/1728 := by
  have h := pauliTriple_integral_one_gap
    (fun t => pauliResidualProduct g t*pauliConditionalIntegral g t)
    (fun t => (1/4:ℝ)*pauliResidualProduct g t) pauliStrictTriple (pauliStrictLoss/8)
    (fun t => by
      have h := mul_le_mul_of_nonneg_left (pauliConditionalIntegral_le_via_incident_holder g hg t)
        (pauliResidualProduct_nonneg g t)
      simpa only [mul_comm] using h)
    (by
      have hcond := mul_le_mul_of_nonneg_left (pauliConditionalIntegral_strict g hg hc)
        (pauliResidualProduct_nonneg g pauliStrictTriple)
      have hloss := mul_le_mul_of_nonneg_left (pauliResidualProduct_strict_lower g hg)
        pauliStrictLoss_pos.le
      nlinarith)
  rw [← pauliFourOverlapIntegral_conditional,integral_const_mul] at h
  have hrest := pauliResidualProduct_integral_le_via_incident_holder g hg
  linarith

/-- The paper's d=2 strict local graph bound uses the same actual finite Pauli readout. -/
theorem pauliFourOverlapIntegral_scaled_le_via_incident_holder (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    16*pauliFourOverlapIntegral g≤pauliLocalKappa := by
  have h := pauliFourOverlapIntegral_strict_via_incident_holder g hg hc
  unfold pauliLocalKappa
  linarith

/-- A single explicit positive κ<1 works for every allowed four-cycle multigraph. -/
theorem pauli_local_graph_contraction_via_incident_holder :
    0<pauliLocalKappa ∧ pauliLocalKappa<1 ∧ ∀ g : FourVertexMultigraph,
      g.IsSixRegular → g.ContainsFourCycle → 16*pauliFourOverlapIntegral g≤pauliLocalKappa :=
  ⟨pauliLocalKappa_pos,pauliLocalKappa_lt_one,pauliFourOverlapIntegral_scaled_le_via_incident_holder⟩


variable (B : CompleteMUB d)

/-- Strict local graph contraction uses the original four-cycle condition, not just six-regularity. -/
theorem completeMUBFourOverlapIntegral_strict_via_incident_holder (hd : 2≤d) (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    completeMUBFourOverlapIntegral B g≤((d:ℝ)⁻¹)^4-
      completeMUBStrictLoss d*((d:ℝ)⁻¹)^3*(((d+1:ℝ)*(d:ℝ))⁻¹)^3 := by
  have h := completeMUBTriple_integral_one_gap
    (fun t => completeMUBResidualProduct B g t*completeMUBConditionalIntegral B g t)
    (fun t => ((d:ℝ)⁻¹)^2*completeMUBResidualProduct B g t)
    (completeMUBStrictTriple d) (completeMUBStrictLoss d*((d:ℝ)⁻¹)^3)
    (fun t => by
      have hh := mul_le_mul_of_nonneg_left (completeMUBConditionalIntegral_le_via_incident_holder B g hg t)
        (completeMUBResidualProduct_nonneg B g t)
      simpa only [mul_comm] using hh)
    (by
      have hcond := mul_le_mul_of_nonneg_left (completeMUBConditionalIntegral_strict B hd g hg hc)
        (completeMUBResidualProduct_nonneg B g (completeMUBStrictTriple d))
      have hloss := mul_le_mul_of_nonneg_left (completeMUBResidualProduct_strict_lower B hd g hg)
        (completeMUBStrictLoss_pos hd).le
      nlinarith)
  rw [← completeMUBFourOverlapIntegral_conditional,integral_const_mul] at h
  have hrest := mul_le_mul_of_nonneg_left (completeMUBResidualProduct_integral_le_via_incident_holder B g hg)
    (sq_nonneg ((d:ℝ)⁻¹))
  nlinarith

theorem completeMUBFourOverlapIntegral_scaled_le_via_incident_holder (hd : 2≤d) (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    (d:ℝ)^4*completeMUBFourOverlapIntegral B g≤completeMUBLocalKappa d := by
  calc
    _ ≤ (d:ℝ)^4*(((d:ℝ)⁻¹)^4-
      completeMUBStrictLoss d*((d:ℝ)⁻¹)^3*(((d+1:ℝ)*(d:ℝ))⁻¹)^3) :=
      mul_le_mul_of_nonneg_left (completeMUBFourOverlapIntegral_strict_via_incident_holder B hd g hg hc)
        (by positivity)
    _ = _ := by
      have hd0 : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
      have hq : (d+1:ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero d
      unfold completeMUBLocalKappa
      field_simp

/-- A single explicit 0<κ<1 works for every allowed graph of the actual supplied MUB records. -/
theorem completeMUB_local_graph_contraction_via_incident_holder (hd : 2≤d) :
    0<completeMUBLocalKappa d ∧ completeMUBLocalKappa d<1 ∧
      ∀ g : FourVertexMultigraph,g.IsSixRegular → g.ContainsFourCycle →
        (d:ℝ)^4*completeMUBFourOverlapIntegral B g≤completeMUBLocalKappa d :=
  ⟨completeMUBLocalKappa_pos,completeMUBLocalKappa_lt_one hd,
    completeMUBFourOverlapIntegral_scaled_le_via_incident_holder B hd⟩

end CertificationGaussian


