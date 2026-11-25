import LocalCertification.Protocol.MeasurableExecutionProductTransport
import LocalCertification.Protocol.ExponentialUpperBound
import LocalCertification.Quantum.CompactTargetTransfer

/-! # Actual upper bounds for measurable product protocol budgets

The original Haar/Pauli basis protocols are genuine members of the enlarged
product protocol class, in every declared universe. Their existing upper event
therefore supplies upper bounds on the actual optimized product budgets.
Only that upper event is used. Inner regularity produces compact canonical
target sets, fixed before every confidence level, with exponential failure.
-/

set_option autoImplicit false
open MeasureTheory Filter Metric CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution.ProductBudget
universe u

/-- The actual basis-subclass upper bound embeds into the full product class;
the expected budget is compared with its own maximum budget. -/
theorem product_budget_upper_exponential (d r : ℕ) (hd : 2 ≤ d) [NeZero d]
    (a b : ℝ) (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hg : gamma ((d : ℝ)+1) r < (a-b)/(1-b)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)), MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad ≤ ENNReal.ofReal (Real.exp (-c*n)) ∧
        ∀ U, U ∉ bad → ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
          expectedBudget.{u} (haarPureVector ψ₀ U) a b δ ≤
            ENat.toENNReal (maximumBudget.{u} (haarPureVector ψ₀ U) a b δ) ∧
          ENat.toENNReal (maximumBudget.{u} (haarPureVector ψ₀ U) a b δ) ≤
            ENNReal.ofReal (C*(n : ℝ)^r*Real.log (1/δ)) := by
  obtain ⟨C,c,hC,hc,hN⟩ := Protocol.qudit_budget_upper_exponential d r hd a b ha hb0 hb1 hg
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [hN] with n hn
  intro ψ₀
  obtain ⟨bad,hm,hp,hbound⟩ := hn ψ₀
  refine ⟨bad,hm,hp,?_⟩
  intro U hU δ hδ hhalf
  refine ⟨expectedBudget_le_maximumBudget _ _ _ _, ?_⟩
  exact (ENat.toENNReal_mono (maximumBudget_le_basisBudget_universe _ _ _ _)).trans
    (hbound U hU δ hδ hhalf).2

/-- One compact set of targets works for every confidence level. The factor
two from inner regularity is absorbed into half the original positive rate. -/
theorem product_budget_upper_sphere_exponential (d r : ℕ) (hd : 2 ≤ d) [NeZero d]
    (a b : ℝ) (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hg : gamma ((d : ℝ)+1) r < (a-b)/(1-b)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∃ good : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1), IsCompact good ∧
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) goodᶜ ≤
          ENNReal.ofReal (Real.exp (-c*n)) ∧
        ∀ ψ ∈ good, ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
          expectedBudget.{u} (spherePureVector ψ) a b δ ≤
            ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
            ENNReal.ofReal (C*(n : ℝ)^r*Real.log (1/δ)) := by
  obtain ⟨C,c,hC,hc,hN⟩ := product_budget_upper_exponential.{u} d r hd a b ha hb0 hb1 hg
  refine ⟨C,c/2,hC,by positivity,?_⟩
  filter_upwards [hN, radialLinear_polynomial_exp_absorb 2 c 0 hc] with n hn habs
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨ψ₀⟩ := NormedSpace.sphere_nonempty_rclike (E := EuclideanSpace ℂ (QuditIndex d n)) ℂ
    (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨bad,hm,hp,hbound⟩ := hn ψ₀
  obtain ⟨good,hcompact,hprob,hfiber⟩ := haar_good_compact_targets (QuditIndex d n) ψ₀
    bad hm (Real.exp (-c*n)) (Real.exp_pos _)
  refine ⟨good,hcompact,?_,?_⟩
  · calc
      _ ≤ complexUnitaryHaar (QuditIndex d n) bad+ENNReal.ofReal (Real.exp (-c*n)) := hprob
      _ ≤ ENNReal.ofReal (Real.exp (-c*n))+ENNReal.ofReal (Real.exp (-c*n)) := add_le_add hp le_rfl
      _ = ENNReal.ofReal (2*Real.exp (-c*n)) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _), two_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [pow_zero, mul_one] using habs)
  · intro ψ hψ δ hδ hhalf
    obtain ⟨U,hU,hUψ⟩ := hfiber ψ hψ
    have h := hbound U hU δ hδ hhalf
    change expectedBudget.{u} (spherePureVector (complexUnitarySphereAction (QuditIndex d n) U ψ₀)) a b δ ≤
      ENat.toENNReal (maximumBudget.{u} (spherePureVector (complexUnitarySphereAction (QuditIndex d n) U ψ₀)) a b δ) ∧
      ENat.toENNReal (maximumBudget.{u} (spherePureVector (complexUnitarySphereAction (QuditIndex d n) U ψ₀)) a b δ) ≤ _ at h
    rw [hUψ] at h
    exact h

/-- A single compact target family has probability tending to one and one
explicit dimension cutoff, preceding every target and every `0 < δ ≤ 1/2`. -/
theorem product_budget_upper_good_family (d r : ℕ) (hd : 2 ≤ d) [NeZero d]
    (a b : ℝ) (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hg : gamma ((d : ℝ)+1) r < (a-b)/(1-b)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
        atTop (nhds 1) ∧
      ∃ N : ℕ, ∀ n ≥ N,
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
          ENNReal.ofReal (Real.exp (-c*n)) ∧
        ∀ ψ ∈ good n, ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
          expectedBudget.{u} (spherePureVector ψ) a b δ ≤
            ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
          ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
            ENNReal.ofReal (C*(n : ℝ)^r*Real.log (1/δ)) := by
  classical
  obtain ⟨C,c,hC,hc,hN⟩ := product_budget_upper_sphere_exponential.{u} d r hd a b ha hb0 hb1 hg
  let P (n : ℕ) (s : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)) : Prop :=
    IsCompact s ∧ canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) sᶜ ≤
      ENNReal.ofReal (Real.exp (-c*n)) ∧
      ∀ ψ ∈ s, ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
        expectedBudget.{u} (spherePureVector ψ) a b δ ≤
          ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
        ENat.toENNReal (maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
          ENNReal.ofReal (C*(n : ℝ)^r*Real.log (1/δ))
  let good (n : ℕ) : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
    if h : ∃ s, P n s then h.choose else ∅
  have hcompact (n : ℕ) : IsCompact (good n) := by
    by_cases h : ∃ s, P n s
    · simpa only [good, dite_eq_left h] using h.choose_spec.1
    · simpa only [good, dite_eq_right h] using isCompact_empty
  have hP : ∀ᶠ n : ℕ in atTop, P n (good n) := by
    filter_upwards [hN] with n hn
    have h : ∃ s, P n s := hn
    simpa only [good, dite_eq_left h] using h.choose_spec
  have hzero : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ)
      atTop (nhds 0) := by
    have ht : Tendsto (fun n : ℕ => Real.exp (-c*n)) atTop (nhds 0) := by
      have he (n : ℕ) : Real.exp (-c*n) = (Real.exp (-c))^n := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      simp_rw [he]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-c)).le
        (Real.exp_lt_one_iff.mpr (by linarith : -c < 0))
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-c*n))) atTop (nhds 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun _ => bot_le)) (hP.mono (fun _ hn => hn.2.1))
  have hone : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
      atTop (nhds 1) := by
    have h := (ENNReal.continuous_sub_left (show (1 : ℝ≥0∞) ≠ ∞ by simp)).continuousAt.tendsto.comp hzero
    have heq (n : ℕ) : 1-canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ =
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n) := by
      let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
      simpa only [compl_compl] using (prob_compl_eq_one_sub (hcompact n).isClosed.measurableSet.compl).symm
    simpa only [Function.comp_def, tsub_zero, heq] using h
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hP.mono (fun _ hn => hn.2))
  exact ⟨C,c,hC,hc,good,hcompact,hone,N,hN⟩

end LocalCertification.Protocol.MeasurableExecution.ProductBudget
