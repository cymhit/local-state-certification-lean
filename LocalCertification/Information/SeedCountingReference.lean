import LocalCertification.Information.FinitePrefixProductDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Information
universe u v

/-- Finite vectors of m slots, represented by nested pairs (the zero vector is PUnit). -/
def FiniteSlots (O : Type v) : ℕ → Type v
  | 0 => PUnit
  | m+1 => FiniteSlots O m × Option O

instance finiteSlotsFintype (O : Type v) [Fintype O] :
    (m : ℕ) → Fintype (FiniteSlots O m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m+1 => by
    letI := finiteSlotsFintype O m
    exact inferInstanceAs (Fintype (FiniteSlots O m × Option O))

instance finiteSlotsMeasurable (O : Type v) [Fintype O] :
    (m : ℕ) → MeasurableSpace (FiniteSlots O m)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | m+1 => by
    letI := finiteSlotsMeasurable O m
    exact inferInstanceAs (MeasurableSpace (FiniteSlots O m × Option O))

instance finiteSlotsSingleton (O : Type v) [Fintype O] :
    (m : ℕ) → MeasurableSingletonClass (FiniteSlots O m)
  | 0 => inferInstanceAs (MeasurableSingletonClass PUnit)
  | m+1 => by
    letI := finiteSlotsSingleton O m
    exact inferInstanceAs (MeasurableSingletonClass (FiniteSlots O m × Option O))

variable {Z : Type u} {O : Type v} [MeasurableSpace Z] [Fintype O]

/-- Keeps the entire original arbitrary measurable seed and groups the finite slots. -/
def flattenHistory : (m : ℕ) → SlotHistory Z O m ≃ᵐ ULift.{v} Z × FiniteSlots O m
  | 0 => MeasurableEquiv.prodPUnit.symm
  | m+1 => (MeasurableEquiv.prodCongr (flattenHistory m)
      (MeasurableEquiv.refl (Option O))).trans MeasurableEquiv.prodAssoc

instance prefixCountingReference_finite (ν : Measure Z) [IsFiniteMeasure ν] :
    (m : ℕ) → IsFiniteMeasure (prefixCountingReference (O := O) ν m)
  | 0 => inferInstanceAs (IsFiniteMeasure (ν.map ULift.up))
  | m+1 => by
    letI := prefixCountingReference_finite ν m
    exact inferInstanceAs (IsFiniteMeasure ((prefixCountingReference (O := O) ν m).prod Measure.count))

theorem count_finiteSlots_succ (m : ℕ) :
    (Measure.count : Measure (FiniteSlots O m)).prod (Measure.count : Measure (Option O)) =
      (Measure.count : Measure (FiniteSlots O (m+1))) := by
  change (Measure.count : Measure (FiniteSlots O m)).prod (Measure.count : Measure (Option O)) =
    (Measure.count : Measure (FiniteSlots O m × Option O))
  apply Measure.ext_of_singleton
  intro h
  rw [show ({h} : Set (FiniteSlots O m × Option O)) = {h.1} ×ˢ {h.2} by ext x; simp]
  rw [Measure.prod_prod]
  simp

theorem flatten_prefixCountingReference (ν : Measure Z) [IsFiniteMeasure ν] (m : ℕ) :
    (prefixCountingReference (O := O) ν m).map (flattenHistory m) =
      (ν.map ULift.up).prod (Measure.count : Measure (FiniteSlots O m)) := by
  induction m with
  | zero =>
    have hc : (Measure.count : Measure PUnit) = Measure.dirac PUnit.unit := by
      apply Measure.ext_of_singleton
      intro h
      simp
    change (ν.map ULift.up).map (fun h => (h, PUnit.unit)) =
      (ν.map ULift.up).prod (Measure.count : Measure PUnit)
    rw [hc, Measure.prod_dirac]
  | succ m ih =>
    change ((prefixCountingReference (O := O) ν m).prod (Measure.count : Measure (Option O))).map
      (MeasurableEquiv.prodAssoc ∘ Prod.map (flattenHistory m) id) =
      (ν.map ULift.up).prod (Measure.count : Measure (FiniteSlots O m × Option O))
    rw [← Measure.map_map MeasurableEquiv.prodAssoc.measurable
        ((flattenHistory m).measurable.prodMap measurable_id),
      ← Measure.map_prod_map _ _ (flattenHistory m).measurable measurable_id,
      Measure.map_id, ih, Measure.prodAssoc_prod, count_finiteSlots_succ]
    rfl

variable [MeasurableSpace O] [MeasurableSingletonClass O]

theorem flatten_prefixLaw_product_density (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] (m : ℕ) :
    (prefixLaw ν κ m).map (flattenHistory m) =
      ((ν.map ULift.up).prod (Measure.count : Measure (FiniteSlots O m))).withDensity
        (fun h => prefixProductDensity κ m ((flattenHistory m).symm h)) := by
  rw [← flatten_prefixCountingReference ν m, ← prefixLaw_withDensity_productDensity ν κ m]
  apply Measure.ext_of_lintegral
  intro f hf
  have hd := measurable_prefixProductDensity κ m
  have hflat := (flattenHistory (Z := Z) (O := O) m).measurable
  have hinv := (flattenHistory (Z := Z) (O := O) m).symm.measurable
  have hfc : Measurable (fun h => f (flattenHistory m h)) := hf.comp hflat
  have hdc : Measurable (fun h => prefixProductDensity κ m ((flattenHistory m).symm h)) :=
    hd.comp hinv
  rw [lintegral_map hf hflat,
    lintegral_withDensity_eq_lintegral_mul _ hd hfc,
    lintegral_withDensity_eq_lintegral_mul _ hdc hf,
    lintegral_map (hdc.mul hf) hflat]
  apply lintegral_congr
  intro h
  simp

/-- Literal original seed version; ULift is removed without discarding any seed information. -/
def originalSeedHistory (m : ℕ) : SlotHistory Z O m ≃ᵐ Z × FiniteSlots O m :=
  (flattenHistory m).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.ulift (MeasurableEquiv.refl _))

theorem originalSeed_prefixCountingReference (ν : Measure Z) [IsFiniteMeasure ν] (m : ℕ) :
    (prefixCountingReference (O := O) ν m).map (originalSeedHistory m) =
      ν.prod (Measure.count : Measure (FiniteSlots O m)) := by
  change (prefixCountingReference (O := O) ν m).map
    (Prod.map ULift.down id ∘ flattenHistory m) = _
  rw [← Measure.map_map (measurable_down.prodMap measurable_id)
      (flattenHistory m).measurable,
    flatten_prefixCountingReference, ← Measure.map_prod_map _ _ measurable_down measurable_id,
    Measure.map_id, Measure.map_map measurable_down measurable_up]
  change (ν.map id).prod Measure.count = _
  rw [Measure.map_id]

theorem originalSeed_prefixLaw_product_density (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] (m : ℕ) :
    (prefixLaw ν κ m).map (originalSeedHistory m) =
      (ν.prod (Measure.count : Measure (FiniteSlots O m))).withDensity
        (fun h => prefixProductDensity κ m ((originalSeedHistory m).symm h)) := by
  rw [← originalSeed_prefixCountingReference ν m, ← prefixLaw_withDensity_productDensity ν κ m]
  apply Measure.ext_of_lintegral
  intro f hf
  have hd := measurable_prefixProductDensity κ m
  have hflat := (originalSeedHistory (Z := Z) (O := O) m).measurable
  have hinv := (originalSeedHistory (Z := Z) (O := O) m).symm.measurable
  have hfc : Measurable (fun h => f (originalSeedHistory m h)) := hf.comp hflat
  have hdc : Measurable (fun h => prefixProductDensity κ m ((originalSeedHistory m).symm h)) :=
    hd.comp hinv
  rw [lintegral_map hf hflat,
    lintegral_withDensity_eq_lintegral_mul _ hd hfc,
    lintegral_withDensity_eq_lintegral_mul _ hdc hf,
    lintegral_map (hdc.mul hf) hflat]
  apply lintegral_congr
  intro h
  simp
end LocalCertification.Information
