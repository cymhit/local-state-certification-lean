import LocalCertification.Information.StoppedKernel

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators LocalCertification.Information
noncomputable section
namespace LocalCertification.Information
universe u v

/-- Recursive primitive histories retain the entire arbitrary-universe seed and every finite slot.
ULift only aligns universes; it does not replace the seed by a finite or standard-Borel space. -/
def SlotHistory (Z : Type u) (O : Type v) : ℕ → Type (max u v)
  | 0 => ULift.{v} Z
  | m+1 => SlotHistory Z O m × Option O

variable {Z : Type u} {O : Type v} [MeasurableSpace Z] [MeasurableSpace O] [Fintype O]
    [MeasurableSingletonClass O]

instance slotHistoryMeasurable : (m : ℕ) → MeasurableSpace (SlotHistory Z O m)
  | 0 => inferInstanceAs (MeasurableSpace (ULift.{v} Z))
  | m+1 => by
    letI := slotHistoryMeasurable m
    exact inferInstanceAs (MeasurableSpace (SlotHistory Z O m × Option O))

/-- The actual finite-prefix laws are iterated compProd measures, with a common initial seed law. -/
def prefixLaw (ν : Measure Z) (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) :
    (m : ℕ) → Measure (SlotHistory Z O m)
  | 0 => ν.map ULift.up
  | m+1 => prefixLaw ν κ m ⊗ₘ κ m

instance prefixLaw_probability (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) [∀ m, IsMarkovKernel (κ m)] :
    (m : ℕ) → IsProbabilityMeasure (prefixLaw ν κ m)
  | 0 => by
    change IsProbabilityMeasure (ν.map ULift.up)
    constructor
    rw [Measure.map_apply measurable_up MeasurableSet.univ]
    simp
  | m+1 => by
    let := prefixLaw_probability ν κ m
    change IsProbabilityMeasure (prefixLaw ν κ m ⊗ₘ κ m)
    infer_instance

omit [MeasurableSpace O] [MeasurableSingletonClass O] in
/-- Exact finite-horizon chain rule with the two generally different history marginals retained. -/
theorem prefixLaw_klDiv_eq_sum (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)] (m : ℕ) :
    klDiv (prefixLaw ν κ m) (prefixLaw ν η m) =
      ∑ t ∈ Finset.range m, ∫⁻ h, klDiv (κ t h) (η t h) ∂prefixLaw ν κ t := by
  induction m with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty]
    change klDiv (prefixLaw ν κ 0) (prefixLaw ν κ 0) = 0
    exact klDiv_self _
  | succ m ih =>
    change klDiv (prefixLaw ν κ m ⊗ₘ κ m) (prefixLaw ν η m ⊗ₘ η m) = _
    rw [klDiv_compProd_eq_add, joint_klDiv_eq_lintegral_full, ih, Finset.sum_range_succ]

/-- The count of active requests over a finite prefix, before identifying it with T∧m for an executor. -/
def prefixActiveCount (s : (m : ℕ) → Set (SlotHistory Z O m)) :
    (m : ℕ) → SlotHistory Z O m → ℝ≥0∞
  | 0 => fun _ => 0
  | m+1 => fun h => prefixActiveCount s m h.1 + (s m).indicator (fun _ => 1) h.1

omit [MeasurableSpace O] [MeasurableSingletonClass O] in
theorem prefixActiveCount_measurable (s : (m : ℕ) → Set (SlotHistory Z O m))
    (hs : ∀ m, MeasurableSet (s m)) (m : ℕ) : Measurable (prefixActiveCount s m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih => exact (ih.comp measurable_fst).add ((measurable_const.indicator (hs m)).comp measurable_fst)

omit [MeasurableSpace O] [MeasurableSingletonClass O] in
/-- Expected active count equals the sum of source-world active probabilities, for every finite horizon. -/
theorem prefixActiveCount_lintegral (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O)) [∀ m, IsMarkovKernel (κ m)]
    (s : (m : ℕ) → Set (SlotHistory Z O m)) (hs : ∀ m, MeasurableSet (s m)) (m : ℕ) :
    (∫⁻ h, prefixActiveCount s m h ∂prefixLaw ν κ m) =
      ∑ t ∈ Finset.range m, prefixLaw ν κ t (s t) := by
  induction m with
  | zero => simp [prefixActiveCount]
  | succ m ih =>
    change (∫⁻ h, prefixActiveCount s m h.1 + (s m).indicator (fun _ => 1) h.1
      ∂(prefixLaw ν κ m ⊗ₘ κ m)) = _
    have hm : Measurable (fun h : SlotHistory Z O m × Option O =>
        prefixActiveCount s m h.1 + (s m).indicator (fun _ => (1 : ℝ≥0∞)) h.1) :=
      ((prefixActiveCount_measurable s hs m).comp measurable_fst).add
        ((measurable_const.indicator (hs m)).comp measurable_fst)
    rw [Measure.lintegral_compProd hm]
    simp only [lintegral_const,measure_univ,mul_one]
    rw [lintegral_add_left (prefixActiveCount_measurable s hs m),ih,
      lintegral_indicator_const (hs m),one_mul,Finset.sum_range_succ]

/-- An arbitrary finite horizon bound. It does not assume finite KL, finite expectation,
absolute continuity, a bounded seed, or that a truncated protocol is valid. -/
theorem prefixLaw_stopped_klDiv_le (ν : Measure Z) [IsProbabilityMeasure ν] [Nonempty O]
    (s : (m : ℕ) → Set (SlotHistory Z O m)) (hs : ∀ m, MeasurableSet (s m))
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) O)
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)] (L : ℝ≥0∞)
    (hL : ∀ m h, h ∈ s m → klDiv (κ m h) (η m h) ≤ L) (m : ℕ) :
    klDiv (prefixLaw ν (fun t => stopContinue (s t) (hs t) (κ t)) m)
      (prefixLaw ν (fun t => stopContinue (s t) (hs t) (η t)) m) ≤
      L * ∫⁻ h, prefixActiveCount s m h
        ∂prefixLaw ν (fun t => stopContinue (s t) (hs t) (κ t)) m := by
  rw [prefixActiveCount_lintegral ν _ s hs, prefixLaw_klDiv_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← joint_klDiv_eq_lintegral_full]
  exact stopped_joint_klDiv_le (s t) (hs t) (κ t) (η t) _ L
    (Filter.Eventually.of_forall (fun h => hL t h))

end LocalCertification.Information
