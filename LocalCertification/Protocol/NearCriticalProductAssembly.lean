import LocalCertification.Information.ConfidenceRange
import CertificationGaussian.HaarOrbit

/-! Common-event, actual Haar, and confidence conversion lemmas used to
assemble the general measurable-product nearcritical corollary. -/
set_option autoImplicit false
open MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

theorem probability_inter_tendsto {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A B : (n : ℕ) → Set (X n)) (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (hlimA : Tendsto (fun n => μ n (A n)) atTop (nhds 1))
    (hlimB : Tendsto (fun n => μ n (B n)) atTop (nhds 1)) :
    Tendsto (fun n => μ n (A n ∩ B n)) atTop (nhds 1) := by
  have hsub := ENNReal.continuous_sub_left (show (1 : ℝ≥0∞) ≠ ∞ by simp)
  have hzA : Tendsto (fun n => μ n (A n)ᶜ) atTop (nhds 0) := by
    have h := hsub.continuousAt.tendsto.comp hlimA
    simpa only [Function.comp_def, prob_compl_eq_one_sub (hA _), tsub_self] using h
  have hzB : Tendsto (fun n => μ n (B n)ᶜ) atTop (nhds 0) := by
    have h := hsub.continuousAt.tendsto.comp hlimB
    simpa only [Function.comp_def, prob_compl_eq_one_sub (hB _), tsub_self] using h
  have hz : Tendsto (fun n => μ n (A n ∩ B n)ᶜ) atTop (nhds 0) := by
    have hsum : Tendsto (fun n => μ n (A n)ᶜ + μ n (B n)ᶜ) atTop (nhds 0) := by
      simpa only [zero_add] using hzA.add hzB
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall (fun _ => bot_le)) (Filter.Eventually.of_forall ?_)
    intro n
    rw [compl_inter]
    exact measure_union_le _ _
  have h := hsub.continuousAt.tendsto.comp hz
  have heq (n : ℕ) : 1 - μ n (A n ∩ B n)ᶜ = μ n (A n ∩ B n) := by
    simpa only [compl_compl] using (prob_compl_eq_one_sub ((hA n).inter (hB n)).compl).symm
  simpa only [Function.comp_def, tsub_zero, heq] using h

theorem choose_compact_good {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    (P : (n : ℕ) → Set (X n) → Prop)
    (hP : ∀ᶠ n : ℕ in atTop, ∃ s : Set (X n), IsCompact s ∧ P n s) :
    ∃ good : (n : ℕ) → Set (X n), (∀ n, IsCompact (good n)) ∧
      ∀ᶠ n : ℕ in atTop, P n (good n) := by
  classical
  let good (n : ℕ) : Set (X n) :=
    if h : ∃ s : Set (X n), IsCompact s ∧ P n s then h.choose else ∅
  refine ⟨good, ?_, ?_⟩
  · intro n
    by_cases h : ∃ s : Set (X n), IsCompact s ∧ P n s
    · simpa only [good, dite_eq_left h] using h.choose_spec.1
    · simpa only [good, dite_eq_right h] using (isCompact_empty : IsCompact (∅ : Set (X n)))
  · filter_upwards [hP] with n hn
    simpa only [good, dite_eq_left hn] using hn.choose_spec.2

theorem compact_good_haar_measure {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (good : Set (sphere (0 : EuclideanSpace ℂ I) 1)) (hc : IsCompact good)
    (ψ₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    IsCompact {U : ComplexUnitary I | complexUnitarySphereAction I U ψ₀ ∈ good} ∧
      complexUnitaryHaar I {U : ComplexUnitary I | complexUnitarySphereAction I U ψ₀ ∈ good} =
        canonicalSphereMeasure (EuclideanSpace ℂ I) good := by
  have hcont := (complexUnitarySphereAction_continuous I).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ComplexUnitary I => ψ₀)))
  refine ⟨(hc.isClosed.preimage hcont).isCompact, ?_⟩
  have he := congrArg (fun μ : Measure (sphere (0 : EuclideanSpace ℂ I) 1) => μ good)
    (complexUnitaryHaar_orbit_map I ψ₀)
  rw [Measure.map_apply (complexUnitarySphereAction_continuous I).measurable.of_uncurry_right
    hc.isClosed.measurableSet] at he
  exact he

theorem nearCritical_confidence_comparison (δstar δ C ε : ℝ) (hs0 : 0 < δstar) (hshalf : δstar < 1/2)
    (hδ : 0 < δ) (hδstar : δ ≤ δstar) (hC : 0 < C) (n j : ℕ) :
    (confidenceFactor δstar/C) * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ) ≤
      (testingThreshold δ/C) * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) := by
  have h := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (testingThreshold_confidence_lower δstar hs0 hshalf δ hδ hδstar) hC.le)
    (show 0 ≤ (n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2) by positivity)
  convert h using 1
  ring

end LocalCertification.Protocol.MeasurableExecution
