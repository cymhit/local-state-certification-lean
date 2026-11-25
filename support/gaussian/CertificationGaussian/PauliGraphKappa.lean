import CertificationGaussian.PauliGraphIntegrals

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian

/-- Two actual records from different Pauli bases, used in the strict-loss event. -/
def pauliRecordE : PauliRecord := (0,0)
def pauliRecordF : PauliRecord := (1,0)

def pauliStrictLoss : ℝ := (5/24)*(1-(Real.sqrt 2)⁻¹)

def pauliLocalKappa : ℝ := 1-pauliStrictLoss/108

theorem pauli_sqrt_inv : (Real.sqrt (2:ℝ))⁻¹=Real.sqrt 2/2 := by
  have hs : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp
  exact (Real.sq_sqrt (by norm_num)).symm

theorem pauliStrictLoss_pos : 0<pauliStrictLoss := by
  have hs : (0:ℝ)<Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h1 : (1:ℝ)<Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have hi : (Real.sqrt (2:ℝ))⁻¹<1 := (inv_lt_one₀ hs).2 h1
  unfold pauliStrictLoss
  positivity

theorem pauliStrictLoss_lt_quarter : pauliStrictLoss<(1/4:ℝ) := by
  have hi : (0:ℝ)<(Real.sqrt (2:ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
  unfold pauliStrictLoss
  linarith

/-- The genuine conditional integral on records (e,e,f), with all six incident edges retained. -/
def pauliMixedSixth (k : ℕ) : ℝ :=
  ∫ s, recordOverlap pauliRecordedUnitVector s pauliRecordE^(6-k) *
    recordOverlap pauliRecordedUnitVector s pauliRecordF^k ∂pauliBasisRecords

theorem pauliMixedSixth_formula (k : ℕ) (hk : 1≤k) (hk5 : k≤5) :
    pauliMixedSixth k =
      ((Real.sqrt 2)⁻¹^k+(Real.sqrt 2)⁻¹^(6-k)+(1/4:ℝ))/6 := by
  unfold pauliMixedSixth
  rw [pauliBasisRecords_integral]
  simp_rw [pauli_record_overlap]
  have hi2 : (Real.sqrt (2:ℝ))⁻¹^2=(1/2:ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hi4 : (Real.sqrt (2:ℝ))⁻¹^4=(1/4:ℝ) := by
    calc
      _ = ((Real.sqrt (2:ℝ))⁻¹^2)^2 := by ring
      _ = _ := by rw [hi2]; norm_num
  have hi6 : (Real.sqrt (2:ℝ))⁻¹^6=(1/8:ℝ) := by
    calc
      _ = ((Real.sqrt (2:ℝ))⁻¹^2)^3 := by ring
      _ = _ := by rw [hi2]; norm_num
  interval_cases k
  all_goals norm_num [pauliRecordE,pauliRecordF,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals norm_num [hi4,hi6]
  all_goals ring

/-- The same positive loss works for each possible incident multiplicity k=1,...,5. -/
theorem pauliMixedSixth_strict_loss (k : ℕ) (hk : 1≤k) (hk5 : k≤5) :
    pauliMixedSixth k ≤ (1/4:ℝ)-pauliStrictLoss := by
  rw [pauliMixedSixth_formula k hk hk5,pauliStrictLoss,pauli_sqrt_inv]
  have hs : (0:ℝ)≤Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt (2:ℝ)^3=2*Real.sqrt 2 := by nlinarith [mul_nonneg hs (sq_nonneg (Real.sqrt 2))]
  have hs4 : Real.sqrt (2:ℝ)^4=4 := by
    calc
      _ = (Real.sqrt (2:ℝ)^2)^2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  have hs5 : Real.sqrt (2:ℝ)^5=4*Real.sqrt 2 := by
    calc
      _ = Real.sqrt (2:ℝ)^4*Real.sqrt 2 := by ring
      _ = _ := by rw [hs4]
  interval_cases k
  all_goals norm_num
  all_goals ring_nf
  all_goals norm_num [hs2,hs3,hs4,hs5]
  all_goals nlinarith

/-- The positive-probability strict-loss event fixes three complete records. -/
def pauliStrictTriple : PauliRecord × (PauliRecord × PauliRecord) :=
  (pauliRecordE,pauliRecordE,pauliRecordF)

theorem pauliConditionalIntegral_strict (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    pauliConditionalIntegral g pauliStrictTriple ≤ (1/4:ℝ)-pauliStrictLoss := by
  have hg0 := hg.1
  have hk : 1≤g.e03 := hc.2.2.2
  have hk5 : g.e03≤5 := by have := hc.1; omega
  have he : g.e01+g.e02=6-g.e03 := by omega
  have hi : pauliConditionalIntegral g pauliStrictTriple=pauliMixedSixth g.e03 := by
    unfold pauliConditionalIntegral pauliMixedSixth
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [pauliIncidentProduct,pauliStrictTriple,← pow_add,he]
  rw [hi]
  exact pauliMixedSixth_strict_loss g.e03 hk hk5

/-- The other six edges retain at least 1/8 on this same concrete event. -/
theorem pauliResidualProduct_strict_lower (g : FourVertexMultigraph) (hg : g.IsSixRegular) :
    (1/8:ℝ)≤pauliResidualProduct g pauliStrictTriple := by
  have hsum : g.e13+g.e23≤6 := by have := hg.2.2.2; omega
  have hr0 : (0:ℝ)≤(Real.sqrt (2:ℝ))⁻¹ := by positivity
  have hr1 : (Real.sqrt (2:ℝ))⁻¹≤1 := by
    rw [pauli_sqrt_inv]
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hr6 : (Real.sqrt (2:ℝ))⁻¹^6=(1/8:ℝ) := by
    calc
      _ = ((Real.sqrt (2:ℝ))⁻¹^2)^3 := by ring
      _ = _ := by rw [inv_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have h := pow_le_pow_of_le_one hr0 hr1 hsum
  rw [hr6] at h
  simpa [pauliResidualProduct,pauliStrictTriple,pauli_record_overlap,
    pauliRecordE,pauliRecordF,pow_add] using h

/-- A single complete triple record has weight 1/216 in the actual reference product measure. -/
theorem pauliTriple_integral_one_gap
    (F H : PauliRecord × (PauliRecord × PauliRecord) → ℝ)
    (t₀ : PauliRecord × (PauliRecord × PauliRecord)) (δ : ℝ)
    (hle : ∀ t,F t≤H t) (hgap : F t₀≤H t₀-δ) :
    (∫ t,F t ∂pauliTripleLaw)≤(∫ t,H t ∂pauliTripleLaw)-δ/216 := by
  rw [pauliTripleLaw_integral_univ,pauliTripleLaw_integral_univ]
  calc
    _ ≤ (1/216:ℝ)*∑ t,(H t-if t=t₀ then δ else 0) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : t=t₀
      · subst t; simpa using hgap
      · simpa [ht] using hle t
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      ring

/-- Strict graph loss for the six actual Pauli records, uniformly in all allowed multiplicities. -/
theorem pauliFourOverlapIntegral_strict (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    pauliFourOverlapIntegral g≤(1/16:ℝ)-pauliStrictLoss/1728 := by
  have h := pauliTriple_integral_one_gap
    (fun t => pauliResidualProduct g t*pauliConditionalIntegral g t)
    (fun t => (1/4:ℝ)*pauliResidualProduct g t) pauliStrictTriple (pauliStrictLoss/8)
    (fun t => by
      have h := mul_le_mul_of_nonneg_left (pauliConditionalIntegral_le g hg t)
        (pauliResidualProduct_nonneg g t)
      simpa only [mul_comm] using h)
    (by
      have hcond := mul_le_mul_of_nonneg_left (pauliConditionalIntegral_strict g hg hc)
        (pauliResidualProduct_nonneg g pauliStrictTriple)
      have hloss := mul_le_mul_of_nonneg_left (pauliResidualProduct_strict_lower g hg)
        pauliStrictLoss_pos.le
      nlinarith)
  rw [← pauliFourOverlapIntegral_conditional,integral_const_mul] at h
  have hrest := pauliResidualProduct_integral_le g hg
  linarith

theorem pauliLocalKappa_pos : 0<pauliLocalKappa := by
  unfold pauliLocalKappa
  linarith [pauliStrictLoss_lt_quarter]

theorem pauliLocalKappa_lt_one : pauliLocalKappa<1 := by
  unfold pauliLocalKappa
  linarith [pauliStrictLoss_pos]

/-- The paper's d=2 strict local graph bound uses the same actual finite Pauli readout. -/
theorem pauliFourOverlapIntegral_scaled_le (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    16*pauliFourOverlapIntegral g≤pauliLocalKappa := by
  have h := pauliFourOverlapIntegral_strict g hg hc
  unfold pauliLocalKappa
  linarith

/-- A single explicit positive κ<1 works for every allowed four-cycle multigraph. -/
theorem pauli_local_graph_contraction :
    0<pauliLocalKappa ∧ pauliLocalKappa<1 ∧ ∀ g : FourVertexMultigraph,
      g.IsSixRegular → g.ContainsFourCycle → 16*pauliFourOverlapIntegral g≤pauliLocalKappa :=
  ⟨pauliLocalKappa_pos,pauliLocalKappa_lt_one,pauliFourOverlapIntegral_scaled_le⟩

end CertificationGaussian
