import CertificationGaussian.HaarGraphKappa

noncomputable section
open MeasureTheory Metric Set
namespace CertificationGaussian.Consumers

/-- The complete full-record conclusion is uniform over all six-regular multigraphs. -/
theorem actual_haar_graph_contraction (d : ℕ) [NeZero d] (hd : 3≤d) :
    0<haarLocalKappa d ∧ haarLocalKappa d<1 ∧
      ∀ g : FourVertexMultigraph, g.IsSixRegular →
        (d:ℝ)^4*haarFourOverlapIntegral d g≤haarLocalKappa d :=
  haar_local_graph_contraction d hd

def disconnectedSixGraph : FourVertexMultigraph := ⟨6,0,0,0,0,6⟩

def mixedSixGraph : FourVertexMultigraph := ⟨1,2,3,3,2,1⟩

theorem disconnectedSixGraph_regular : disconnectedSixGraph.IsSixRegular := by
  norm_num [FourVertexMultigraph.IsSixRegular,disconnectedSixGraph]

theorem disconnectedSixGraph_no_cycle : ¬disconnectedSixGraph.ContainsFourCycle := by
  norm_num [FourVertexMultigraph.ContainsFourCycle,disconnectedSixGraph]

/-- Two disjoint sixfold edges attain the unscaled m6² bound, testing independence and multiplicity. -/
theorem disconnectedSixGraph_exact (d : ℕ) [NeZero d] :
    haarFourOverlapIntegral d disconnectedSixGraph =
      (6/((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2)))^2 := by
  unfold haarFourOverlapIntegral
  simp_rw [disconnectedSixGraph.overlapProduct_matchings
    (haarRecordedUnitVector d) disconnectedSixGraph_regular]
  simp only [disconnectedSixGraph,pow_zero,mul_one]
  exact matchingOverlap01_sixth (haarBasisRecords d) (haarRecordedUnitVector d)
    (haarRecordedUnitVector_continuous d) _ (fun a => haarBasisRecords_overlap_sixth d _)

theorem mixedSixGraph_regular_cycle : mixedSixGraph.IsSixRegular ∧ mixedSixGraph.ContainsFourCycle := by
  norm_num [FourVertexMultigraph.IsSixRegular,FourVertexMultigraph.ContainsFourCycle,mixedSixGraph]

/-- A true nonuniform-multiplicity four-cycle, with exact d=3 strict κ=81/100. -/
theorem mixedSixGraph_dimension_three :
    81*haarFourOverlapIntegral 3 mixedSixGraph ≤ 81/100 := by
  have h := haarFourOverlapIntegral_scaled_le 3 mixedSixGraph mixedSixGraph_regular_cycle.1
  norm_num [haarLocalKappa] at h ⊢
  exact h

/-- Haar κ equals one in dimensions one and two; no strict d=2 claim is made. -/
theorem haar_kappa_low_dimensions : haarLocalKappa 1=1 ∧ haarLocalKappa 2=1 := by
  norm_num [haarLocalKappa]

/-- Every actual d=1 record has sixth overlap one, including its full Haar-basis component. -/
theorem haar_record_dimension_one (b : sphere (0 : EuclideanSpace ℂ (Fin 1)) 1) :
    (∫ ω, ‖inner ℂ b.val (haarRecordedUnitVector 1 ω).val‖^6 ∂haarBasisRecords 1)=1 := by
  have h := haarBasisRecords_overlap_sixth 1 b
  norm_num at h
  exact h

/-- Zero-dimensional real radial sixth moment remains zero. -/
theorem real_radial_dimension_zero :
    (∫ x : EuclideanSpace ℝ (Fin 0), ‖x‖^6 ∂ProbabilityTheory.stdGaussian _)=0 := by
  simpa using stdGaussian_norm_sixth_moment (I := Fin 0)

end CertificationGaussian.Consumers
