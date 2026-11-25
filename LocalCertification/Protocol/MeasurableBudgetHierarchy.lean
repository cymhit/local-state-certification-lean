import LocalCertification.Protocol.MeasurablePowerLowerBound
import LocalCertification.Protocol.MeasurableProductUpper
import LocalCertification.Protocol.SameConfidenceEvent
import LocalCertification.Information.ContinuousConfidenceRatio

/-! # The tolerance hierarchy for measurable product protocols

The lower bound for arbitrary product POVMs uses one calibrated pair on the common
all-frame event. The upper bound uses a protocol from the same measurement class.
The compact target family and size cutoff precede the confidence parameter.
Only the probability-limit lemma from `SameConfidenceEvent` is needed here.
-/

set_option autoImplicit false
open MeasureTheory Filter Metric CertificationGaussian LocalCertification.Information
  LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Asymptotic
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u

/-- Exact testing-scale bounds hold simultaneously on one compact,
exponentially typical set for the full measurable product protocol class. -/
theorem product_budget_sphere_eventually (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C cprob : ℝ, 0<c ∧ 0<C ∧ 0<cprob ∧ ∀ᶠ n : ℕ in atTop,
      ∃ good : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1), IsCompact good ∧
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) goodᶜ ≤
          ENNReal.ofReal (Real.exp (-cprob*n)) ∧
        ∀ ψ∈good, ∀ δ : ℝ, 0<δ → δ<1/2 →
          ENNReal.ofReal (c*(n:ℝ)^r*testingThreshold δ) ≤ expectedBudget.{u} (spherePureVector ψ) a b δ ∧
          expectedBudget.{u} (spherePureVector ψ) a b δ ≤ ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
            ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  have hb1 : b<1 := hab.trans_le ha
  have hq : 1<(d:ℝ)+1 := by
    have : (2:ℝ)≤d := by exact_mod_cast hd
    linarith
  have hg : 0<(a-b)/(1-b) := div_pos (sub_pos.mpr hab) (sub_pos.mpr hb1)
  have hu : gamma ((d:ℝ)+1) r < (a-b)/(1-b) := criticalDegree_spec _ hq _ hg
  have hl : r=0 ∨ (a-b)/(1-b)≤gamma ((d:ℝ)+1) (r-1) := by
    by_cases hr : r=0
    · exact Or.inl hr
    · exact Or.inr (criticalDegree_bracket _ hq _ hg (by omega : 0<r)).2
  obtain ⟨C,cu,hC,hcu,hup⟩ := product_budget_upper_sphere_exponential.{u} d r hd a b ha hb.le hb1 hu
  obtain ⟨c,cl,hc,hcl,hlo⟩ := product_budget_power_lower_eventually.{u} d r hd a b ha hb hb1 hl
  let rate := min cu cl
  have hrate : 0<rate := lt_min hcu hcl
  refine ⟨c,C,rate/2,hc,hC,by positivity,?_⟩
  filter_upwards [hup,hlo,radialLinear_polynomial_exp_absorb 2 rate 0 hrate] with n hnup hnlo hnabs
  obtain ⟨Gup,hcup,hpup,hupper⟩ := hnup
  obtain ⟨Glo,hclo,hplo,hlower⟩ := hnlo
  have hpup' : canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) Gupᶜ ≤
      ENNReal.ofReal (Real.exp (-rate*n)) := by
    apply hpup.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hle : rate≤cu := min_le_left _ _
    nlinarith [show (0:ℝ)≤n from Nat.cast_nonneg n]
  have hplo' : canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) Gloᶜ ≤
      ENNReal.ofReal (Real.exp (-rate*n)) := by
    apply hplo.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hle : rate≤cl := min_le_right _ _
    nlinarith [show (0:ℝ)≤n from Nat.cast_nonneg n]
  refine ⟨Gup∩Glo,(hcup.isClosed.inter hclo.isClosed).isCompact,?_,?_⟩
  · rw [Set.compl_inter]
    calc
      _ ≤ canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) Gupᶜ +
          canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) Gloᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-rate*n))+ENNReal.ofReal (Real.exp (-rate*n)) := add_le_add hpup' hplo'
      _ = ENNReal.ofReal (2*Real.exp (-rate*n)) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _),two_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [pow_zero,mul_one] using hnabs)
  · intro ψ hψ δ hδ hhalf
    exact ⟨(hlower ψ hψ.2 δ hδ hhalf).1,hupper ψ hψ.1 δ hδ hhalf.le⟩

/-- One global compact target family and a positive dimension cutoff give the
exact lower factor on all of `(0,1/2)`, together with the logarithmic upper bound. -/
theorem product_budget_sphere_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ c C cprob : ℝ, 0<c ∧ 0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
    ∃ N : ℕ, 1≤N ∧ ∀ n, N≤n →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (Real.exp (-cprob*n)) ∧
      ∀ ψ∈good n, ∀ δ : ℝ, 0<δ → δ<1/2 →
        ENNReal.ofReal (c*(n:ℝ)^r*testingThreshold δ) ≤ expectedBudget.{u} (spherePureVector ψ) a b δ ∧
        expectedBudget.{u} (spherePureVector ψ) a b δ ≤ ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  classical
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  obtain ⟨c,C,cprob,hc,hC,hcprob,hN⟩ := product_budget_sphere_eventually.{u} d hd a b hb hab ha
  let P (n : ℕ) (s : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)) : Prop :=
    IsCompact s ∧ canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) sᶜ ≤
      ENNReal.ofReal (Real.exp (-cprob*n)) ∧
    ∀ ψ∈s, ∀ δ : ℝ, 0<δ → δ<1/2 →
      ENNReal.ofReal (c*(n:ℝ)^r*testingThreshold δ) ≤ expectedBudget.{u} (spherePureVector ψ) a b δ ∧
      expectedBudget.{u} (spherePureVector ψ) a b δ ≤ ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
      ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
        ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ))
  let good (n : ℕ) : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
    if h : ∃ s, P n s then h.choose else ∅
  have hcompact (n : ℕ) : IsCompact (good n) := by
    by_cases h : ∃ s, P n s
    · simpa only [good,dite_eq_left h] using h.choose_spec.1
    · simpa only [good,dite_eq_right h] using isCompact_empty
  have hP : ∀ᶠ n : ℕ in atTop, P n (good n) := by
    filter_upwards [hN] with n hn
    have h : ∃ s, P n s := hn
    simpa only [good,dite_eq_left h] using h.choose_spec
  have hone := Protocol.canonicalSphere_good_probability_tendsto_one d hd good hcompact cprob hcprob
    (hP.mono (fun _ hn => hn.2.1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hP.mono (fun _ hn => hn.2))
  refine ⟨c,C,cprob,hc,hC,hcprob,good,hcompact,hone,max N 1,le_max_right _ _,?_⟩
  intro n hn
  exact hN n ((le_max_left N 1).trans hn)

/-- The same target family, failure rate and cutoff work for every fixed
confidence cutoff below one half; only the positive lower constant changes. -/
theorem product_budget_same_event_confidence_hierarchy (d : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (hb : 0<b) (hab : b<a) (ha : a≤1) :
    let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
    ∃ C cprob : ℝ, 0<C ∧ 0<cprob ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) atTop (nhds 1) ∧
    ∃ N : ℕ, 1≤N ∧
      (∀ n, N≤n → canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (Real.exp (-cprob*n))) ∧
      ∀ δstar : ℝ, 0<δstar → δstar<1/2 → ∃ c : ℝ, 0<c ∧
        ∀ n, N≤n → ∀ ψ∈good n, ∀ δ : ℝ, 0<δ → δ≤δstar →
          ENNReal.ofReal (c*(n:ℝ)^r*Real.log (1/δ)) ≤ expectedBudget.{u} (spherePureVector ψ) a b δ ∧
          expectedBudget.{u} (spherePureVector ψ) a b δ ≤ ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
            ENNReal.ofReal (C*(n:ℝ)^r*Real.log (1/δ)) := by
  dsimp only
  let r := criticalDegree ((d:ℝ)+1) ((a-b)/(1-b))
  obtain ⟨A,C,cprob,hA,hC,hcprob,good,hcompact,hone,N,hNpos,hN⟩ :=
    product_budget_sphere_hierarchy.{u} d hd a b hb hab ha
  refine ⟨C,cprob,hC,hcprob,good,hcompact,hone,N,hNpos,fun n hn => (hN n hn).1,?_⟩
  intro δstar hs0 hshalf
  obtain ⟨k, hk, hcompare⟩ := testingThreshold_confidence_lower_via_continuous_ratio δstar hs0 hshalf
  refine ⟨A*k, mul_pos hA hk, ?_⟩
  intro n hn ψ hψ δ hδ hcut
  obtain ⟨hlo,hmid,hup⟩ := (hN n hn).2 ψ hψ δ hδ (hcut.trans_lt hshalf)
  refine ⟨?_,hmid,hup⟩
  apply (ENNReal.ofReal_le_ofReal ?_).trans hlo
  have h := mul_le_mul_of_nonneg_left
    (hcompare δ hδ hcut)
    (show (0:ℝ)≤A*(n:ℝ)^r by positivity)
  convert h using 1
  ring

end LocalCertification.Protocol.MeasurableExecution.ProductBudget
