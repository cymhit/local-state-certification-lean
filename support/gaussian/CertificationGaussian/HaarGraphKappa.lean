import CertificationGaussian.FourVertexOverlap

noncomputable section
open MeasureTheory Metric Set
namespace CertificationGaussian

/-- The actual graph integral over four independent full Haar basis/outcome records. -/
def haarFourOverlapIntegral (d : ℕ) [NeZero d] (g : FourVertexMultigraph) : ℝ :=
  ∫ x, g.overlapProduct (haarRecordedUnitVector d) x ∂fourReadoutLaw (haarBasisRecords d)

/-- The explicit dimension-only constant for the Haar local ensemble. -/
def haarLocalKappa (d : ℕ) : ℝ := 36*(d:ℝ)^2/(((d:ℝ)+1)^2*((d:ℝ)+2)^2)

/-- The graph bound uses the proved actual Haar sixth moment, with no moment assumption. -/
theorem haarFourOverlapIntegral_le (d : ℕ) [NeZero d]
    (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    haarFourOverlapIntegral d g ≤ (6/((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2)))^2 := by
  exact g.overlap_integral_le (haarBasisRecords d) (haarRecordedUnitVector d) hg
    (haarRecordedUnitVector_continuous d) _ (fun a => haarBasisRecords_overlap_sixth d _)

/-- Exact normalization in the paper's graph bound; it also applies without a four-cycle. -/
theorem haarFourOverlapIntegral_scaled_le (d : ℕ) [NeZero d]
    (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    (d:ℝ)^4*haarFourOverlapIntegral d g ≤ haarLocalKappa d := by
  have h := mul_le_mul_of_nonneg_left (haarFourOverlapIntegral_le d g hg)
    (show (0:ℝ)≤(d:ℝ)^4 by positivity)
  have he : (d:ℝ)^4*(6/((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2)))^2 = haarLocalKappa d := by
    have hd : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
    unfold haarLocalKappa
    field_simp
    ring
  exact h.trans_eq he

theorem haarLocalKappa_pos (d : ℕ) (hd : 0<d) : 0<haarLocalKappa d := by
  unfold haarLocalKappa
  have : (0:ℝ)<d := by exact_mod_cast hd
  positivity

/-- Strict contraction holds for every Haar local dimension at least three. -/
theorem haarLocalKappa_lt_one (d : ℕ) (hd : 3≤d) : haarLocalKappa d<1 := by
  have hD : (3:ℝ)≤d := by exact_mod_cast hd
  unfold haarLocalKappa
  apply (div_lt_one (by positivity)).mpr
  have hp : (0:ℝ)<((d:ℝ)-1)*((d:ℝ)-2)*((d:ℝ)^2+9*(d:ℝ)+2) := by
    apply mul_pos (mul_pos (by linarith) (by linarith))
    positivity
  nlinarith

/-- The complete local Haar graph conclusion, with κ fixed before the graph. -/
theorem haar_local_graph_contraction (d : ℕ) [NeZero d] (hd : 3≤d) :
    0<haarLocalKappa d ∧ haarLocalKappa d<1 ∧
      ∀ (g : FourVertexMultigraph), g.IsSixRegular →
        (d:ℝ)^4*haarFourOverlapIntegral d g ≤ haarLocalKappa d := by
  refine ⟨haarLocalKappa_pos d (by omega),haarLocalKappa_lt_one d hd,?_⟩
  intro g hg
  exact haarFourOverlapIntegral_scaled_le d g hg

end CertificationGaussian
