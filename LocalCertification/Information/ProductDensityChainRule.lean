import LocalCertification.Information.FiniteAtomLogIntegrability
set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Information
universe u v
variable {Z : Type u} {O : Type v} [MeasurableSpace Z] [MeasurableSpace O]
  [Fintype O] [MeasurableSingletonClass O]

def prefixProductLikelihood
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) :
    (m : ℕ) → SlotHistory Z O m → ℝ≥0∞
  | 0 => fun _ => 1
  | m+1 => fun h => prefixProductLikelihood κ η m h.1 * atomDensity (κ m h.1) (η m h.1) h.2

def prefixLogLikelihoodSum
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) :
    (m : ℕ) → SlotHistory Z O m → ℝ
  | 0 => fun _ => 0
  | m+1 => fun h => prefixLogLikelihoodSum κ η m h.1 + slotLogLikelihood (κ m) (η m) h

theorem measurable_prefixProductLikelihood
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) (m : ℕ) :
    Measurable (prefixProductLikelihood κ η m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih => exact (ih.comp measurable_fst).mul (measurable_jointDensity (κ m) (η m))

theorem prefixProductLikelihood_ne_top
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) (m : ℕ)
    (h : SlotHistory Z O m) : prefixProductLikelihood κ η m h ≠ ∞ := by
  induction m with
  | zero => exact ENNReal.one_ne_top
  | succ m ih => exact ENNReal.mul_ne_top (ih h.1) ENNReal.ofReal_ne_top

theorem prefixProductLikelihood_mul_density
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)]
    (hAC : ∀ t h, κ t h ≪ η t h) (m : ℕ) (h : SlotHistory Z O m) :
    prefixProductLikelihood κ η m h * prefixProductDensity η m h =
      prefixProductDensity κ m h := by
  induction m with
  | zero => simp [prefixProductLikelihood, prefixProductDensity]
  | succ m ih =>
    change (prefixProductLikelihood κ η m h.1 * atomDensity (κ m h.1) (η m h.1) h.2) *
        (prefixProductDensity η m h.1 * η m h.1 {h.2}) =
        prefixProductDensity κ m h.1 * κ m h.1 {h.2}
    calc
      _ = (prefixProductLikelihood κ η m h.1 * prefixProductDensity η m h.1) *
          (atomDensity (κ m h.1) (η m h.1) h.2 * η m h.1 {h.2}) := by ac_rfl
      _ = _ := by rw [ih h.1, atomDensity_mul (hAC m h.1)]

theorem prefixLaw_withDensity_productLikelihood (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)]
    (hAC : ∀ t h, κ t h ≪ η t h) (m : ℕ) :
    (prefixLaw ν η m).withDensity (prefixProductLikelihood κ η m) = prefixLaw ν κ m := by
  rw [← prefixLaw_withDensity_productDensity ν η m, ← withDensity_mul
    _ (measurable_prefixProductDensity η m) (measurable_prefixProductLikelihood κ η m)]
  have he : (prefixProductDensity η m * prefixProductLikelihood κ η m) =
      prefixProductDensity κ m := by
    funext h
    change prefixProductDensity η m h * prefixProductLikelihood κ η m h = _
    rw [mul_comm]
    exact prefixProductLikelihood_mul_density κ η hAC m h
  rw [he, prefixLaw_withDensity_productDensity]

theorem prefixProductLikelihood_log_expand
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) (m : ℕ)
    (h : SlotHistory Z O m) (hpos : prefixProductLikelihood κ η m h ≠ 0) :
    Real.log (prefixProductLikelihood κ η m h).toReal = prefixLogLikelihoodSum κ η m h := by
  induction m with
  | zero => simp [prefixProductLikelihood, prefixLogLikelihoodSum]
  | succ m ih =>
    change prefixProductLikelihood κ η m h.1 * atomDensity (κ m h.1) (η m h.1) h.2 ≠ 0 at hpos
    have ha := (mul_ne_zero_iff.mp hpos).1
    have hb := (mul_ne_zero_iff.mp hpos).2
    change Real.log (prefixProductLikelihood κ η m h.1 * atomDensity (κ m h.1) (η m h.1) h.2).toReal = _
    rw [ENNReal.toReal_mul, Real.log_mul
      (ENNReal.toReal_ne_zero.mpr ⟨ha, prefixProductLikelihood_ne_top κ η m h.1⟩)
      (ENNReal.toReal_ne_zero.mpr ⟨hb, ENNReal.ofReal_ne_top⟩), ih h.1 ha]
    simp [prefixLogLikelihoodSum, atomDensity, slotLogLikelihood,
      ENNReal.toReal_ofReal (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]

theorem measurable_prefixLogLikelihoodSum
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) (m : ℕ) :
    Measurable (prefixLogLikelihoodSum κ η m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih => exact (ih.comp measurable_fst).add (measurable_slotLogLikelihood (κ m) (η m))

theorem prefixLogLikelihoodSum_integrable (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)]
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ t h, klDiv (κ t h) (η t h) ≤ L) (m : ℕ) :
    Integrable (prefixLogLikelihoodSum κ η m) (prefixLaw ν κ m) := by
  induction m with
  | zero => exact integrable_const 0
  | succ m ih =>
    have hi : Integrable (fun h : SlotHistory Z O m × Option O => prefixLogLikelihoodSum κ η m h.1)
        (prefixLaw ν κ m ⊗ₘ κ m) := by
      apply (Measure.integrable_compProd_iff
        ((measurable_prefixLogLikelihoodSum κ η m).comp measurable_fst).aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall fun h => by simpa only [Function.comp_apply] using (integrable_const (prefixLogLikelihoodSum κ η m h) : Integrable (fun _ : Option O => prefixLogLikelihoodSum κ η m h) (κ m h))
      · simpa using ih.norm
    exact hi.add (integrable_slotLogLikelihood _ (κ m) (η m) L hfinite (hL m))

theorem prefixLogLikelihoodSum_integral (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)]
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ t h, klDiv (κ t h) (η t h) ≤ L) (m : ℕ) :
    (∫ h, prefixLogLikelihoodSum κ η m h ∂prefixLaw ν κ m) =
      ∑ t ∈ Finset.range m, ∫ h, (klDiv (κ t h) (η t h)).toReal ∂prefixLaw ν κ t := by
  induction m with
  | zero => simp [prefixLogLikelihoodSum]
  | succ m ih =>
    have hi := prefixLogLikelihoodSum_integrable ν κ η L hfinite hL m
    have hif : Integrable (fun h : SlotHistory Z O m × Option O => prefixLogLikelihoodSum κ η m h.1)
        (prefixLaw ν κ m ⊗ₘ κ m) := by
      apply (Measure.integrable_compProd_iff
        ((measurable_prefixLogLikelihoodSum κ η m).comp measurable_fst).aestronglyMeasurable).mpr
      exact ⟨Filter.Eventually.of_forall (fun h => by simpa only [Function.comp_apply] using (integrable_const (prefixLogLikelihoodSum κ η m h) : Integrable (fun _ : Option O => prefixLogLikelihoodSum κ η m h) (κ m h))), by simpa using hi.norm⟩
    change (∫ h, prefixLogLikelihoodSum κ η m h.1 + slotLogLikelihood (κ m) (η m) h
      ∂(prefixLaw ν κ m ⊗ₘ κ m)) = _
    rw [integral_add hif (integrable_slotLogLikelihood _ (κ m) (η m) L hfinite (hL m)),
      integral_slotLogLikelihood _ (κ m) (η m) L hfinite (hL m), Measure.integral_compProd hif]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rw [ih, Finset.sum_range_succ]


theorem prefix_llr_eq_logLikelihoodSum (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)]
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ t h, klDiv (κ t h) (η t h) ≤ L) (m : ℕ) :
    llr (prefixLaw ν κ m) (prefixLaw ν η m) =ᵐ[prefixLaw ν κ m] prefixLogLikelihoodSum κ η m := by
  have hc : ∀ t h, κ t h ≪ η t h := fun t h =>
    (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top hfinite (hL t h))).1
  have he := prefixLaw_withDensity_productLikelihood ν κ η hc m
  have hrn := Measure.rnDeriv_withDensity (prefixLaw ν η m)
    (measurable_prefixProductLikelihood κ η m)
  rw [he] at hrn
  have hac := prefixLaw_ac_of_finite_bound_product_density ν κ η L hfinite hL m
  have hp : ∀ᵐ h ∂prefixLaw ν κ m, prefixProductLikelihood κ η m h ≠ 0 := by
    rw [← he, ae_withDensity_iff (measurable_prefixProductLikelihood κ η m)]
    exact Filter.Eventually.of_forall fun _ hh => hh
  filter_upwards [hac.ae_le hrn, hp] with h hr hp
  rw [llr, hr]
  exact prefixProductLikelihood_log_expand κ η m h hp

/-- Paper-route finite chain equality: explicit product density, log expansion,
the total negative part bound, uniform integrability, then Fubini. -/
theorem prefixLaw_klDiv_eq_sum_product_density (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)]
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ t h, klDiv (κ t h) (η t h) ≤ L) (m : ℕ) :
    klDiv (prefixLaw ν κ m) (prefixLaw ν η m) =
      ∑ t ∈ Finset.range m, ∫⁻ h, klDiv (κ t h) (η t h) ∂prefixLaw ν κ t := by
  have ha := prefixLaw_ac_of_finite_bound_product_density ν κ η L hfinite hL m
  have he := prefix_llr_eq_logLikelihoodSum ν κ η L hfinite hL m
  have hi := (prefixLogLikelihoodSum_integrable ν κ η L hfinite hL m).congr he.symm
  rw [klDiv_of_ac_of_integrable ha hi]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right]
  rw [integral_congr_ae he, prefixLogLikelihoodSum_integral ν κ η L hfinite hL m,
    ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro t ht
    have hmeas := (measurable_conditionalKL_full (κ t) (η t)).ennreal_toReal
    have hint : Integrable (fun h => (klDiv (κ t h) (η t h)).toReal) (prefixLaw ν κ t) := by
      apply Integrable.of_bound hmeas.aestronglyMeasurable L.toReal
      exact Filter.Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono hfinite (hL t h)
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    apply lintegral_congr
    intro h
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top hfinite (hL t h))
  · intro t ht
    exact integral_nonneg fun _ => ENNReal.toReal_nonneg

/-- The stopped finite-prefix bound obtained through the paper route, including an
empty active set at time zero and the common empty-slot kernels thereafter. -/
theorem prefixLaw_stopped_klDiv_le_product_density (ν : Measure Z) [IsProbabilityMeasure ν] [Nonempty O]
    (s : (m : ℕ) → Set (SlotHistory Z O m)) (hs : ∀ m, MeasurableSet (s m))
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) O)
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)] (L : ℝ≥0∞)
    (hfinite : L ≠ ∞) (hL : ∀ m h, h ∈ s m → klDiv (κ m h) (η m h) ≤ L) (m : ℕ) :
    klDiv (prefixLaw ν (fun t => stopContinue (s t) (hs t) (κ t)) m)
      (prefixLaw ν (fun t => stopContinue (s t) (hs t) (η t)) m) ≤
      L * ∫⁻ h, prefixActiveCount s m h
        ∂prefixLaw ν (fun t => stopContinue (s t) (hs t) (κ t)) m := by
  have hb : ∀ t h, klDiv (stopContinue (s t) (hs t) (κ t) h)
      (stopContinue (s t) (hs t) (η t) h) ≤ L := by
    intro t h
    rw [stopContinue_kl]
    by_cases hh : h ∈ s t
    · simpa [hh] using hL t h hh
    · simp [hh]
  rw [prefixActiveCount_lintegral ν _ s hs,
    prefixLaw_klDiv_eq_sum_product_density ν _ _ L hfinite hb, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  calc
    _ ≤ ∫⁻ h, (s t).indicator (fun _ => L) h
        ∂prefixLaw ν (fun t => stopContinue (s t) (hs t) (κ t)) t := by
      apply lintegral_mono
      intro h
      dsimp only
      rw [stopContinue_kl]
      by_cases hh : h ∈ s t
      · simpa [hh] using hL t h hh
      · simp [hh]
    _ = _ := lintegral_indicator_const (hs t) L

end LocalCertification.Information
