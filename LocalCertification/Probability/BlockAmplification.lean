import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace LocalCertification.Probability

/-- The literal empirical mean of m independent copies of one real score. -/
def blockMean {Ω : Type*} (f : Ω → ℝ) (m : ℕ) (x : Fin m → Ω) : ℝ :=
  (m:ℝ)⁻¹ * ∑ i, f (x i)

/-- The number of copies in one block at variance bound V and score separation Δ. -/
def blockCopies (V Δ : ℝ) : ℕ := ⌈128*V/Δ^2⌉₊

/-- The smallest odd integer at least eight times the confidence logarithm. -/
def blockCount (δ : ℝ) : ℕ :=
  let c := ⌈8*Real.log (1/δ)⌉₊
  if Even c then c+1 else c

theorem blockCopies_pos {V Δ : ℝ} (hV : 0<V) (hΔ : 0<Δ) : 0<blockCopies V Δ := by
  have h := Nat.le_ceil (128*V/Δ^2)
  have hp : (0:ℝ)<128*V/Δ^2 := by positivity
  have hc : (0:ℝ)<(blockCopies V Δ:ℝ) := hp.trans_le h
  exact_mod_cast hc

theorem blockCopies_upper {V Δ : ℝ} (hV : 1≤V) (hΔ : 0<Δ) (hΔ1 : Δ≤1) :
    (blockCopies V Δ:ℝ)≤129*V/Δ^2 := by
  have hs : 0<Δ^2 := sq_pos_of_pos hΔ
  have hratio : 1≤V/Δ^2 := (le_div_iff₀ hs).mpr (by nlinarith)
  have hc := Nat.ceil_lt_add_one (show 0≤128*V/Δ^2 by positivity)
  change (⌈128*V/Δ^2⌉₊:ℝ)≤_
  have he : 128*V/Δ^2+V/Δ^2=129*V/Δ^2 := by ring
  linarith

theorem blockCopies_chebyshev_constant {V Δ : ℝ} (hV : 0<V) (hΔ : 0<Δ) :
    16*V/((blockCopies V Δ:ℝ)*Δ^2)≤1/8 := by
  have hm : (0:ℝ)<blockCopies V Δ := by exact_mod_cast blockCopies_pos hV hΔ
  have hc : 128*V≤(blockCopies V Δ:ℝ)*Δ^2 :=
    (div_le_iff₀ (sq_pos_of_pos hΔ)).mp (Nat.le_ceil (128*V/Δ^2))
  apply (div_le_iff₀ (mul_pos hm (sq_pos_of_pos hΔ))).mpr
  nlinarith

theorem blockCount_odd (δ : ℝ) : Odd (blockCount δ) := by
  dsimp only [blockCount]
  split_ifs with h
  · exact Nat.not_even_iff_odd.mp (by simpa only [Nat.even_add_one,not_not] using h)
  · exact Nat.not_even_iff_odd.mp h

theorem blockCount_ge (δ : ℝ) : 8*Real.log (1/δ)≤(blockCount δ:ℝ) := by
  have h := Nat.le_ceil (8*Real.log (1/δ))
  dsimp only [blockCount]
  split_ifs <;> push_cast <;> linarith

theorem blockCount_le_of_odd {δ : ℝ} {k : ℕ} (hk : Odd k)
    (h : 8*Real.log (1/δ)≤(k:ℝ)) : blockCount δ≤k := by
  have hc : ⌈8*Real.log (1/δ)⌉₊≤k := Nat.ceil_le.mpr h
  dsimp only [blockCount]
  split_ifs with he
  · have hn : ⌈8*Real.log (1/δ)⌉₊≠k := by
      intro eq
      exact (Nat.not_even_iff_odd.mpr hk) (eq ▸ he)
    omega
  · exact hc

theorem blockCount_lt {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) :
    (blockCount δ:ℝ)<8*Real.log (1/δ)+2 := by
  have hl : 0≤Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by simpa using hδ1))
  have hc := Nat.ceil_lt_add_one (show 0≤8*Real.log (1/δ) by positivity)
  dsimp only [blockCount]
  split_ifs <;> push_cast <;> linarith


/-- Oddness gives a genuinely nonempty set of blocks for every argument. -/
theorem blockCount_pos (δ : ℝ) : 0<blockCount δ := by
  obtain ⟨k,hk⟩ := blockCount_odd δ
  omega

/-- The exact Hoeffding exponent at the chosen number of blocks is below the requested error. -/
theorem blockCount_confidence {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    Real.exp (-9*(blockCount δ:ℝ)/32)≤δ := by
  have hl : 0≤Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hk := blockCount_ge δ
  calc
    _ ≤ Real.exp (-Real.log (1/δ)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = δ := by rw [one_div,Real.log_inv,neg_neg,Real.exp_log hδ]

/-- One universal logarithmic bound covers the entire required confidence range, including δ>1/3. -/
theorem blockCount_budget {δ : ℝ} (hδ : 0<δ) (hδhalf : δ≤1/2) :
    (blockCount δ:ℝ)≤12*Real.log (1/δ) := by
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<(2:ℝ)⁻¹ by norm_num)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hl := Real.log_le_log (show (0:ℝ)<2 by norm_num)
    ((le_div_iff₀ hδ).mpr (by linarith : (2:ℝ)*δ≤1))
  have hk := blockCount_lt hδ (show δ≤1 by linarith)
  linarith

/-- Deterministic copy budget of the exact 128/odd-log construction. -/
theorem block_total_budget {V Δ δ : ℝ} (hV : 1≤V) (hΔ : 0<Δ) (hΔ1 : Δ≤1)
    (hδ : 0<δ) (hδhalf : δ≤1/2) :
    ((blockCopies V Δ*blockCount δ:ℕ):ℝ)≤1548*V/Δ^2*Real.log (1/δ) := by
  rw [Nat.cast_mul]
  have hk := blockCount_budget hδ hδhalf
  have hm := blockCopies_upper hV hΔ hΔ1
  calc
    _ ≤ (129*V/Δ^2)*(12*Real.log (1/δ)) :=
      mul_le_mul hm hk (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

section Copies
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ)

theorem blockMean_memLp (hf : MemLp f 2 μ) (m : ℕ) :
    MemLp (blockMean f m) 2 (Measure.pi (fun _ : Fin m => μ)) := by
  exact (memLp_finsetSum Finset.univ (fun i _ =>
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => μ) i))).const_mul _

theorem blockMean_integral (hf : MemLp f 2 μ) {m : ℕ} (hm : 0<m) :
    ∫ x,blockMean f m x∂Measure.pi (fun _ : Fin m => μ)=∫ x,f x∂μ := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hi (i : Fin m) : Integrable (fun x : Fin m → Ω => f (x i)) (Measure.pi (fun _ : Fin m => μ)) :=
    (hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => μ) i)).integrable (by norm_num)
  have he (i : Fin m) : (∫ x : Fin m → Ω,f (x i)∂Measure.pi (fun _ : Fin m => μ))=∫ x,f x∂μ := by
    have hp := measurePreserving_eval (fun _ : Fin m => μ) i
    have hfm : AEStronglyMeasurable f ((Measure.pi (fun _ : Fin m => μ)).map (fun x => x i)) := by
      rw [hp.map_eq]
      exact hf.aestronglyMeasurable
    rw [← integral_map hp.measurable.aemeasurable hfm,hp.map_eq]
  unfold blockMean
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem blockMean_variance (hf : MemLp f 2 μ) {m : ℕ} (hm : 0<m) :
    variance (blockMean f m) (Measure.pi (fun _ : Fin m => μ))=variance f μ/(m:ℝ) := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  unfold blockMean
  rw [variance_const_mul]
  have hv := variance_sum_pi (μ:=fun _ : Fin m => μ) (X:=fun _ => f) (fun _ => hf)
  have he : (fun x : Fin m → Ω => ∑ i, f (x i)) =
      (∑ i : Fin m, fun x : Fin m → Ω => f (x i)) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he,hv]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

/-- Chebyshev's inequality for the mean of the independent scores in a single block. -/
theorem blockMean_chebyshev (hf : MemLp f 2 μ) {V Δ : ℝ} (hV : 0<V) (hΔ : 0<Δ)
    (hv : variance f μ≤V) :
    Measure.pi (fun _ : Fin (blockCopies V Δ) => μ)
      {x | Δ/4≤|blockMean f (blockCopies V Δ) x-(∫ y,f y∂μ)|}≤ENNReal.ofReal (1/8) := by
  let m := blockCopies V Δ
  have hm : 0<m := blockCopies_pos hV hΔ
  have hm0 : (0:ℝ)<m := by exact_mod_cast hm
  have h := meas_ge_le_variance_div_sq (blockMean_memLp μ f hf m) (show 0<Δ/4 by positivity)
  rw [blockMean_integral μ f hf hm,blockMean_variance μ f hf hm] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    variance f μ/(m:ℝ)/(Δ/4)^2 ≤ V/(m:ℝ)/(Δ/4)^2 := by gcongr
    _ = 16*V/((m:ℝ)*Δ^2) := by field_simp; ring
    _ ≤ 1/8 := blockCopies_chebyshev_constant hV hΔ


/-- The actual empirical vote uses the prescribed scalar threshold. -/
def blockVote (t : ℝ) (m : ℕ) (x : Fin m → Ω) : Fin 2 :=
  if t≤blockMean f m x then 1 else 0

theorem blockMean_measurable (hf : Measurable f) (m : ℕ) : Measurable (blockMean f m) := by
  unfold blockMean
  fun_prop

theorem blockVote_measurable (hf : Measurable f) (t : ℝ) (m : ℕ) :
    Measurable (blockVote f t m) := by
  unfold blockVote
  exact measurable_const.piecewise (measurableSet_le measurable_const (blockMean_measurable f hf m)) measurable_const

/-- The accepting class has the literal wrong-vote probability at most 1/8. -/
theorem blockVote_error_high (hf : MemLp f 2 μ) {V Δ t : ℝ} (hV : 0<V) (hΔ : 0<Δ)
    (hv : variance f μ≤V) (hmean : t+Δ/4≤∫ y,f y∂μ) :
    Measure.pi (fun _ : Fin (blockCopies V Δ) => μ)
      {x | blockVote f t (blockCopies V Δ) x≠1}≤ENNReal.ofReal (1/8) := by
  refine (measure_mono ?_).trans (blockMean_chebyshev μ f hf hV hΔ hv)
  intro x hx
  have ht : blockMean f (blockCopies V Δ) x<t := by
    by_contra h
    have he : blockVote f t (blockCopies V Δ) x=1 := by simp [blockVote,not_lt.mp h]
    exact hx he
  have ha := le_abs_self (-(blockMean f (blockCopies V Δ) x-(∫ y,f y∂μ)))
  rw [abs_neg] at ha
  change Δ/4≤|blockMean f (blockCopies V Δ) x-(∫ y,f y∂μ)|
  linarith

/-- The rejecting class has the same bound, including empirical threshold ties. -/
theorem blockVote_error_low (hf : MemLp f 2 μ) {V Δ t : ℝ} (hV : 0<V) (hΔ : 0<Δ)
    (hv : variance f μ≤V) (hmean : (∫ y,f y∂μ)+Δ/4≤t) :
    Measure.pi (fun _ : Fin (blockCopies V Δ) => μ)
      {x | blockVote f t (blockCopies V Δ) x≠0}≤ENNReal.ofReal (1/8) := by
  refine (measure_mono ?_).trans (blockMean_chebyshev μ f hf hV hΔ hv)
  intro x hx
  have ht : t≤blockMean f (blockCopies V Δ) x := by
    by_contra h
    have he : blockVote f t (blockCopies V Δ) x=0 := by simp [blockVote,h]
    exact hx he
  have ha := le_abs_self (blockMean f (blockCopies V Δ) x-(∫ y,f y∂μ))
  change Δ/4≤|blockMean f (blockCopies V Δ) x-(∫ y,f y∂μ)|
  linarith

end Copies


/-- Literal finite majority; ties choose one, and never arise for the prescribed odd count. -/
def majorityVote {k : ℕ} (v : Fin k → Fin 2) : Fin 2 :=
  if k≤2*(Finset.univ.filter (fun i => v i=1)).card then 1 else 0

/-- The actual zero-one error indicator of a vote against either promised class. -/
def voteError (j v : Fin 2) : ℝ := if v=j then 0 else 1

theorem voteError_zero (v : Fin 2) : voteError 0 v=if v=1 then (1:ℝ) else 0 := by
  fin_cases v <;> norm_num [voteError]

theorem voteError_one (v : Fin 2) : voteError 1 v=1-voteError 0 v := by
  fin_cases v <;> norm_num [voteError]

theorem voteError_mem (j v : Fin 2) : voteError j v∈Set.Icc (0:ℝ) 1 := by
  unfold voteError
  split_ifs <;> norm_num

theorem voteError_sum_zero {k : ℕ} (v : Fin k → Fin 2) :
    (∑ i,voteError 0 (v i))=((Finset.univ.filter (fun i => v i=1)).card:ℝ) := by
  simp only [voteError_zero,Finset.sum_boole]

/-- A wrong literal majority requires at least half of the component votes to be wrong. -/
theorem majority_wrong_subset {k : ℕ} (v : Fin k → Fin 2) (j : Fin 2)
    (hj : majorityVote v≠j) : (k:ℝ)/2≤∑ i,voteError j (v i) := by
  fin_cases j
  · change (k:ℝ)/2≤∑ i,voteError 0 (v i)
    change majorityVote v≠0 at hj
    have hk : k≤2*(Finset.univ.filter (fun i => v i=1)).card := by
      by_contra h
      exact hj (by simp [majorityVote,h])
    rw [voteError_sum_zero]
    have hc : (k:ℝ)≤2*((Finset.univ.filter (fun i => v i=1)).card:ℝ) := by exact_mod_cast hk
    linarith
  · change (k:ℝ)/2≤∑ i,voteError 1 (v i)
    change majorityVote v≠1 at hj
    have hk : ¬k≤2*(Finset.univ.filter (fun i => v i=1)).card := by
      intro h
      exact hj (by simp [majorityVote,h])
    simp only [voteError_one,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one,voteError_sum_zero]
    have hc : 2*((Finset.univ.filter (fun i => v i=1)).card:ℝ)<(k:ℝ) := by exact_mod_cast (not_le.mp hk)
    linarith

theorem majorityVote_measurable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (v : Fin k → Ω → Fin 2) (hv : ∀ i,Measurable (v i)) :
    Measurable (fun ω => majorityVote (fun i => v i ω)) := by
  exact (measurable_of_countable majorityVote).comp (measurable_pi_iff.mpr hv)

section Majority
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Independent [0,1]-valued error indicators with means at most 1/8 obey the exact note exponent. -/
theorem independent_majority_tail {k : ℕ} (hk : 0<k) (X : Fin k → Ω → ℝ)
    (hi : iIndepFun X μ) (hXm : ∀ i,AEMeasurable (X i) μ)
    (hb : ∀ i,∀ᵐ ω∂μ,X i ω∈Set.Icc (0:ℝ) 1)
    (he : ∀ i,(∫ ω,X i ω∂μ)≤1/8) :
    μ {ω | (k:ℝ)/2≤∑ i,X i ω}≤ENNReal.ofReal (Real.exp (-9*(k:ℝ)/32)) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  let Y := fun i ω => X i ω-(∫ z,X i z∂μ)
  have hY : iIndepFun Y μ := hi.comp (fun i y => y-(∫ z,X i z∂μ)) (by intro i; fun_prop)
  have hc (i : Fin k) : HasSubgaussianMGF (Y i) (1/4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hXm i) (hb i)
    convert h using 1
    norm_num
  have hs := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY
    (s:=Finset.univ) (c:=fun _ => (1/4:ℝ≥0)) (fun i _ => hc i)
    (ε:=3*(k:ℝ)/8) (by positivity)
  have hmeans : (∑ i,∫ z,X i z∂μ)≤(k:ℝ)/8 := by
    calc
      _ ≤ ∑ _i : Fin k,(1/8:ℝ) := Finset.sum_le_sum (fun i _ => he i)
      _ = _ := by simp; ring
  have hsub : {ω | (k:ℝ)/2≤∑ i,X i ω}⊆{ω | 3*(k:ℝ)/8≤∑ i,Y i ω} := by
    intro ω hω
    change 3*(k:ℝ)/8≤∑ i,(X i ω-(∫ z,X i z∂μ))
    rw [Finset.sum_sub_distrib]
    change (k:ℝ)/2≤∑ i,X i ω at hω
    linarith
  have hr := (measureReal_mono hsub).trans hs
  have hexp : -(3*(k:ℝ)/8)^2/(2*(↑(∑ _i : Fin k,(1/4:ℝ≥0)):ℝ)) = -9*(k:ℝ)/32 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    field_simp [hk0.ne']
    ring
  rw [hexp] at hr
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hr


omit [IsProbabilityMeasure μ] in
/-- The actual wrong-vote indicator integrates to its actual event probability. -/
theorem voteError_integral (v : Ω → Fin 2) (hv : Measurable v) (j : Fin 2) :
    (∫ ω,voteError j (v ω)∂μ)=μ.real {ω | v ω≠j} := by
  have hm : MeasurableSet {ω | v ω≠j} := (measurableSet_eq_fun hv measurable_const).compl
  have he : (fun ω => voteError j (v ω))=Set.indicator {ω | v ω≠j} (fun _ => (1:ℝ)) := by
    funext ω
    by_cases h : v ω=j <;> simp [voteError,h]
  rw [he,integral_indicator hm,integral_const]
  simp

/-- An actual product of k independent complete block samples supports the literal majority test. -/
theorem iid_majority_error (v : Ω → Fin 2) (hv : Measurable v) (j : Fin 2)
    (he : μ {ω | v ω≠j}≤ENNReal.ofReal (1/8)) {k : ℕ} (hk : 0<k) :
    Measure.pi (fun _ : Fin k => μ) {x | majorityVote (fun i => v (x i))≠j}≤
      ENNReal.ofReal (Real.exp (-9*(k:ℝ)/32)) := by
  let E := fun ω => voteError j (v ω)
  let X := fun (i : Fin k) (x : Fin k → Ω) => E (x i)
  let M := Measure.pi (fun _ : Fin k => μ)
  have hE : Measurable E := (measurable_of_countable (voteError j)).comp hv
  have hmean : (∫ ω,E ω∂μ)≤1/8 := by
    rw [voteError_integral μ v hv j]
    have h := ENNReal.toReal_mono (show ENNReal.ofReal (1/8:ℝ)≠⊤ by simp) he
    simpa only [measureReal_def,ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1/8)] using h
  have hi : iIndepFun X M := iIndepFun_pi (fun _ => hE.aemeasurable)
  have hXm (i : Fin k) : AEMeasurable (X i) M :=
    (hE.comp (measurable_pi_apply i)).aemeasurable
  have hXb (i : Fin k) : ∀ᵐ x∂M,X i x∈Set.Icc (0:ℝ) 1 :=
    Filter.Eventually.of_forall (fun x => voteError_mem j (v (x i)))
  have hXe (i : Fin k) : (∫ x,X i x∂M)≤1/8 := by
    have hp := measurePreserving_eval (fun _ : Fin k => μ) i
    have hfm : AEStronglyMeasurable E (M.map (fun x => x i)) := by
      rw [hp.map_eq]
      exact hE.aestronglyMeasurable
    change (∫ x,E (x i)∂M)≤1/8
    rw [← integral_map hp.measurable.aemeasurable hfm,hp.map_eq]
    exact hmean
  refine (measure_mono ?_).trans (independent_majority_tail M hk X hi hXm hXb hXe)
  intro x hx
  exact majority_wrong_subset (fun i => v (x i)) j hx

/-- The actual two-level finite score test: empirical threshold votes followed by literal majority. -/
def scoreMajorityTest (f : Ω → ℝ) (t : ℝ) (m k : ℕ) (x : Fin k → Fin m → Ω) : Fin 2 :=
  majorityVote (fun i => blockVote f t m (x i))

theorem scoreMajorityTest_measurable (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) (m k : ℕ) :
    Measurable (scoreMajorityTest f t m k) := by
  exact majorityVote_measurable (fun (i : Fin k) (x : Fin k → Fin m → Ω) => blockVote f t m (x i))
    (fun i => (blockVote_measurable f hf t m).comp (measurable_pi_apply i))

/-- The concrete test achieves error δ in the high-mean class on the actual iid copy law. -/
theorem scoreMajority_error_high (f : Ω → ℝ) (hfm : Measurable f) (hf : MemLp f 2 μ)
    {V Δ t δ : ℝ} (hV : 0<V) (hΔ : 0<Δ) (hδ : 0<δ) (hδ1 : δ<1)
    (hv : variance f μ≤V) (hmean : t+Δ/4≤∫ y,f y∂μ) :
    Measure.pi (fun _ : Fin (blockCount δ) => Measure.pi (fun _ : Fin (blockCopies V Δ) => μ))
      {x | scoreMajorityTest f t (blockCopies V Δ) (blockCount δ) x≠1}≤ENNReal.ofReal δ := by
  exact (iid_majority_error (Measure.pi (fun _ : Fin (blockCopies V Δ) => μ))
    (blockVote f t (blockCopies V Δ)) (blockVote_measurable f hfm t _) 1
    (blockVote_error_high μ f hf hV hΔ hv hmean) (blockCount_pos δ)).trans
      (ENNReal.ofReal_le_ofReal (blockCount_confidence hδ hδ1))

/-- The same explicit test achieves error δ in the low-mean class, including vote ties. -/
theorem scoreMajority_error_low (f : Ω → ℝ) (hfm : Measurable f) (hf : MemLp f 2 μ)
    {V Δ t δ : ℝ} (hV : 0<V) (hΔ : 0<Δ) (hδ : 0<δ) (hδ1 : δ<1)
    (hv : variance f μ≤V) (hmean : (∫ y,f y∂μ)+Δ/4≤t) :
    Measure.pi (fun _ : Fin (blockCount δ) => Measure.pi (fun _ : Fin (blockCopies V Δ) => μ))
      {x | scoreMajorityTest f t (blockCopies V Δ) (blockCount δ) x≠0}≤ENNReal.ofReal δ := by
  exact (iid_majority_error (Measure.pi (fun _ : Fin (blockCopies V Δ) => μ))
    (blockVote f t (blockCopies V Δ)) (blockVote_measurable f hfm t _) 0
    (blockVote_error_low μ f hf hV hΔ hv hmean) (blockCount_pos δ)).trans
      (ENNReal.ofReal_le_ofReal (blockCount_confidence hδ hδ1))

end Majority

namespace Consumers

/-- The exact prescribed size in the unit-variance, unit-gap fixture is 128, with no integer slack lost. -/
theorem blockCopies_one_one : blockCopies 1 1=128 := by norm_num [blockCopies]

/-- Empty empirical sums stay explicit; the probability theorems demand a positive actual block size. -/
theorem blockMean_empty {Ω : Type*} (f : Ω → ℝ) (x : Fin 0 → Ω) : blockMean f 0 x=0 := by
  simp [blockMean]

/-- A genuine nonconstant bounded score on a two-point single-copy outcome space. -/
def twoPointScore (x : Fin 2) : ℝ := x.val

theorem twoPointScore_memLp (μ : Measure (Fin 2)) [IsProbabilityMeasure μ] :
    MemLp twoPointScore 2 μ := by
  apply MemLp.of_bound (measurable_of_countable twoPointScore).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro x
  change ‖(x.val:ℝ)‖≤1
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (show x.val≤1 by omega)

/-- One and the same explicit test works under two different actual input laws, for all required errors. -/
theorem twoPoint_same_test_errors {δ : ℝ} (hδ : 0<δ) (hδhalf : δ≤1/2) :
    Measure.pi (fun _ : Fin (blockCount δ) =>
      Measure.pi (fun _ : Fin 128 => Measure.dirac (0:Fin 2)))
      {x | scoreMajorityTest twoPointScore (1/2) 128 (blockCount δ) x≠0}≤ENNReal.ofReal δ ∧
    Measure.pi (fun _ : Fin (blockCount δ) =>
      Measure.pi (fun _ : Fin 128 => Measure.dirac (1:Fin 2)))
      {x | scoreMajorityTest twoPointScore (1/2) 128 (blockCount δ) x≠1}≤ENNReal.ofReal δ := by
  have hl := scoreMajority_error_low (Measure.dirac (0:Fin 2)) twoPointScore
    (measurable_of_countable _) (twoPointScore_memLp _) (V:=1) (Δ:=1) (t:=1/2)
    (by norm_num) (by norm_num) hδ (by linarith)
    (by simp [variance_dirac]) (by simp [integral_dirac,twoPointScore]; norm_num)
  have hh := scoreMajority_error_high (Measure.dirac (1:Fin 2)) twoPointScore
    (measurable_of_countable _) (twoPointScore_memLp _) (V:=1) (Δ:=1) (t:=1/2)
    (by norm_num) (by norm_num) hδ (by linarith)
    (by simp [variance_dirac]) (by simp [integral_dirac,twoPointScore]; norm_num)
  have hm := blockCopies_one_one
  generalize blockCopies 1 1 = m at hl hh hm
  subst m
  exact ⟨hl,hh⟩

/-- The same two-point test has the logarithmic deterministic copy budget through δ=1/2. -/
theorem twoPoint_budget {δ : ℝ} (hδ : 0<δ) (hδhalf : δ≤1/2) :
    ((128*blockCount δ:ℕ):ℝ)≤1548*Real.log (1/δ) := by
  simpa only [blockCopies_one_one,one_pow,mul_one,div_one] using
    block_total_budget (V:=1) (Δ:=1) (by norm_num) (by norm_num) (by norm_num) hδ hδhalf

end Consumers
end LocalCertification.Probability
