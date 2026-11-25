import CertificationGaussian.CompleteMUBStrictLoss

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian
variable {d : ℕ} [NeZero d]

/-- Concrete, distinct basis labels from the supplied complete MUB ensemble. -/
def completeMUBRecordE (d : ℕ) [NeZero d] : CompleteMUBRecord d := (0,0)
def completeMUBRecordF (d : ℕ) [NeZero d] : CompleteMUBRecord d :=
  (⟨1,Nat.succ_lt_succ (NeZero.pos d)⟩,0)

theorem completeMUBRecord_basis_ne :
    (completeMUBRecordE d).1≠(completeMUBRecordF d).1 := by
  intro h
  have he := congrArg Fin.val h
  norm_num [completeMUBRecordE,completeMUBRecordF] at he

def completeMUBStrictTriple (d : ℕ) [NeZero d] :
    CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d) :=
  (completeMUBRecordE d,completeMUBRecordE d,completeMUBRecordF d)

variable (B : CompleteMUB d)

theorem completeMUBConditionalIntegral_strict (hd : 2≤d) (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    completeMUBConditionalIntegral B g (completeMUBStrictTriple d)≤
      ((d:ℝ)⁻¹)^2-completeMUBStrictLoss d := by
  have hg0 := hg.1
  have hk : 1≤g.e03 := hc.2.2.2
  have hk5 : g.e03≤5 := by have := hc.1; omega
  have he : g.e01+g.e02=6-g.e03 := by omega
  have hi : completeMUBConditionalIntegral B g (completeMUBStrictTriple d)=
      completeMUBMixedSixth B (completeMUBRecordE d) (completeMUBRecordF d) g.e03 := by
    unfold completeMUBConditionalIntegral completeMUBMixedSixth
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [completeMUBIncidentProduct,completeMUBStrictTriple,← pow_add,he]
  rw [hi]
  exact completeMUBMixedSixth_strict_loss B hd _ _ completeMUBRecord_basis_ne g.e03 hk hk5

theorem completeMUBResidualProduct_strict_lower (hd : 2≤d) (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) :
    ((d:ℝ)⁻¹)^3≤completeMUBResidualProduct B g (completeMUBStrictTriple d) := by
  have hsum : g.e13+g.e23≤6 := by have := hg.2.2.2; omega
  have ht0 := (completeMUBAmplitude_pos (d:=d)).le
  have ht1 := (completeMUBAmplitude_lt_one hd).le
  have h := pow_le_pow_of_le_one ht0 ht1 hsum
  rw [completeMUBAmplitude_sixth] at h
  simpa [completeMUBResidualProduct,completeMUBStrictTriple,completeMUB_overlap,
    completeMUBRecord_basis_ne,completeMUBAmplitude,pow_add] using h

/-- The strict event is an actual atom of the full triple record measure, of mass N^-3. -/
theorem completeMUBTriple_integral_one_gap
    (F H : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d) → ℝ)
    (t₀ : CompleteMUBRecord d × (CompleteMUBRecord d × CompleteMUBRecord d)) (δ : ℝ)
    (hle : ∀ t,F t≤H t) (hgap : F t₀≤H t₀-δ) :
    (∫ t,F t∂completeMUBTripleLaw d)≤
      (∫ t,H t∂completeMUBTripleLaw d)-δ*(((d+1:ℝ)*(d:ℝ))⁻¹)^3 := by
  rw [completeMUBTripleLaw_integral_univ,completeMUBTripleLaw_integral_univ]
  calc
    _ ≤ (((d+1:ℝ)*(d:ℝ))⁻¹)^3*∑ t,(H t-if t=t₀ then δ else 0) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : t=t₀
      · subst t; simpa using hgap
      · simpa [ht] using hle t
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      ring

/-- Strict local graph contraction uses the original four-cycle condition, not just six-regularity. -/
theorem completeMUBFourOverlapIntegral_strict (hd : 2≤d) (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    completeMUBFourOverlapIntegral B g≤((d:ℝ)⁻¹)^4-
      completeMUBStrictLoss d*((d:ℝ)⁻¹)^3*(((d+1:ℝ)*(d:ℝ))⁻¹)^3 := by
  have h := completeMUBTriple_integral_one_gap
    (fun t => completeMUBResidualProduct B g t*completeMUBConditionalIntegral B g t)
    (fun t => ((d:ℝ)⁻¹)^2*completeMUBResidualProduct B g t)
    (completeMUBStrictTriple d) (completeMUBStrictLoss d*((d:ℝ)⁻¹)^3)
    (fun t => by
      have hh := mul_le_mul_of_nonneg_left (completeMUBConditionalIntegral_le B g hg t)
        (completeMUBResidualProduct_nonneg B g t)
      simpa only [mul_comm] using hh)
    (by
      have hcond := mul_le_mul_of_nonneg_left (completeMUBConditionalIntegral_strict B hd g hg hc)
        (completeMUBResidualProduct_nonneg B g (completeMUBStrictTriple d))
      have hloss := mul_le_mul_of_nonneg_left (completeMUBResidualProduct_strict_lower B hd g hg)
        (completeMUBStrictLoss_pos hd).le
      nlinarith)
  rw [← completeMUBFourOverlapIntegral_conditional,integral_const_mul] at h
  have hrest := mul_le_mul_of_nonneg_left (completeMUBResidualProduct_integral_le B g hg)
    (sq_nonneg ((d:ℝ)⁻¹))
  nlinarith

theorem completeMUBFourOverlapIntegral_scaled_le (hd : 2≤d) (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    (d:ℝ)^4*completeMUBFourOverlapIntegral B g≤completeMUBLocalKappa d := by
  calc
    _ ≤ (d:ℝ)^4*(((d:ℝ)⁻¹)^4-
      completeMUBStrictLoss d*((d:ℝ)⁻¹)^3*(((d+1:ℝ)*(d:ℝ))⁻¹)^3) :=
      mul_le_mul_of_nonneg_left (completeMUBFourOverlapIntegral_strict B hd g hg hc)
        (by positivity)
    _ = _ := by
      have hd0 : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
      have hq : (d+1:ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero d
      unfold completeMUBLocalKappa
      field_simp

/-- A single explicit 0<κ<1 works for every allowed graph of the actual supplied MUB records. -/
theorem completeMUB_local_graph_contraction (hd : 2≤d) :
    0<completeMUBLocalKappa d ∧ completeMUBLocalKappa d<1 ∧
      ∀ g : FourVertexMultigraph,g.IsSixRegular → g.ContainsFourCycle →
        (d:ℝ)^4*completeMUBFourOverlapIntegral B g≤completeMUBLocalKappa d :=
  ⟨completeMUBLocalKappa_pos,completeMUBLocalKappa_lt_one hd,
    completeMUBFourOverlapIntegral_scaled_le B hd⟩

end CertificationGaussian
