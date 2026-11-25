import LocalCertification.Protocol.IndependentRecords

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical Set
open scoped BigOperators ENNReal
noncomputable section
namespace LocalCertification.Protocol
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {O : Type v} [MeasurableSpace O]

omit [Fintype ι] in
/-- Replacing one coordinate by a fresh draw is measurable in the original product sigma algebra. -/
theorem coordinateUpdate_measurable (i : ι) :
    Measurable (fun p : (ι → O) × O => Function.update p.1 i p.2) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j=i
  · subst j; simpa using (measurable_snd : Measurable (fun p : (ι → O) × O => p.2))
  · simpa [Function.update_of_ne h, Function.comp_def] using ((measurable_pi_apply j).comp measurable_fst :
      Measurable (fun p : (ι → O) × O => p.1 j))

/-- An independent coordinate refresh leaves the literal finite product law invariant. -/
theorem pi_map_coordinateUpdate (μ : ι → Measure O) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    ((Measure.pi μ).prod (μ i)).map (fun p => Function.update p.1 i p.2) = Measure.pi μ := by
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (coordinateUpdate_measurable i) (MeasurableSet.univ_pi hs)]
  have he : (fun p : (ι → O) × O => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (fun j => if j=i then Set.univ else s j)) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro hp
      constructor
      · intro j
        by_cases h : j=i
        · simp [h]
        · simpa [h, Function.update_of_ne h] using hp j
      · simpa using hp i
    · rintro ⟨hp,hi⟩ j
      by_cases h : j=i
      · subst j; simpa using hi
      · simpa [h, Function.update_of_ne h] using hp j
  rw [he, Measure.prod_prod, Measure.pi_pi]
  have hp : (∏ j, μ j (if j=i then Set.univ else s j)) = ∏ j ∈ Finset.univ.erase i, μ j (s j) := by
    rw [← Finset.prod_erase_mul _ _ (a:=i) (by simp)]
    simp only [↓reduceIte, measure_univ, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
  rw [hp, Finset.prod_erase_mul _ _ (by simp)]

/-- Exact conditional resampling identity; no integrability or finite-valued-function hypothesis is imposed. -/
theorem lintegral_pi_coordinate_resample (μ : ι → Measure O) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (F : (ι → O) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂Measure.pi μ) =
      ∫⁻ x, ∫⁻ o, F (Function.update x i o) ∂μ i ∂Measure.pi μ := by
  calc
    _ = ∫⁻ p, F (Function.update p.1 i p.2) ∂(Measure.pi μ).prod (μ i) := by
      nth_rw 1 [← pi_map_coordinateUpdate μ i]
      exact lintegral_map hF (coordinateUpdate_measurable i)
    _ = _ := lintegral_prod _ (hF.comp (coordinateUpdate_measurable i)).aemeasurable

end LocalCertification.Protocol
