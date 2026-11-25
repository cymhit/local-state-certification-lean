import LocalCertification.Information.BinaryKLMonotonicity
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Terminal information from finite measurable records

Finite decision events converge under each input's own almost-sure termination
law. Binary relative entropy is lower semicontinuous at all probability pairs,
including singular boundary pairs. Monotone convergence of the actual truncated
cost then retains infinite expected stopping times. The prefix-law identities
and one-step bounds are supplied separately by a physical executor.
-/

set_option autoImplicit false
open MeasureTheory InformationTheory Set Filter
open scoped ENNReal Topology
noncomputable section

namespace LocalCertification.Information.KernelTerminal

variable {X : Type*} [MeasurableSpace X]

/-- A finite report includes a decision only after its actual stopping time. -/
def truncatedDecisionEvent (T : X → ℕ∞) (D : X → Fin 2) (j : Fin 2) (m : ℕ) : Set X :=
  {x | T x ≤ (m : ℕ∞) ∧ D x = j}

theorem truncatedDecisionEvent_measurable (T : X → ℕ∞) (D : X → Fin 2)
    (hT : Measurable T) (hD : Measurable D) (j : Fin 2) (m : ℕ) :
    MeasurableSet (truncatedDecisionEvent T D j m) :=
  (hT (Set.to_countable (Set.Iic (m : ℕ∞))).measurableSet).inter
    (hD (measurableSet_singleton j))

omit [MeasurableSpace X] in
theorem truncatedDecisionEvent_mono (T : X → ℕ∞) (D : X → Fin 2) (j : Fin 2) :
    Monotone (truncatedDecisionEvent T D j) := by
  intro m k hmk x hx
  exact ⟨hx.1.trans (Nat.cast_le.mpr hmk), hx.2⟩

omit [MeasurableSpace X] in
theorem iUnion_truncatedDecisionEvent (T : X → ℕ∞) (D : X → Fin 2) (j : Fin 2) :
    (⋃ m : ℕ, truncatedDecisionEvent T D j m) = {x | T x ≠ ⊤ ∧ D x = j} := by
  ext x
  simp only [Set.mem_iUnion, truncatedDecisionEvent, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, hj⟩
    exact ⟨ne_top_of_le_ne_top (WithTop.natCast_ne_top m) hm, hj⟩
  · rintro ⟨ht, hj⟩
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ht
    exact ⟨m, hm.ge, hj⟩

/-- No finite expected-time assumption is needed for convergence of decisions. -/
theorem truncatedDecisionEvent_probability_tendsto (P : Measure X) [IsProbabilityMeasure P]
    (T : X → ℕ∞) (D : X → Fin 2) (hTP : ∀ᵐ x ∂P, T x ≠ ⊤) (j : Fin 2) :
    Tendsto (fun m => P.real (truncatedDecisionEvent T D j m)) atTop
      (𝓝 (P.real {x | D x = j})) := by
  have hu : P (⋃ m : ℕ, truncatedDecisionEvent T D j m) = P {x | D x = j} := by
    rw [iUnion_truncatedDecisionEvent]
    apply measure_congr
    filter_upwards [hTP] with x hx
    exact propext (and_iff_right hx)
  have ht := tendsto_measure_iUnion_atTop (μ := P) (truncatedDecisionEvent_mono T D j)
  rw [hu] at ht
  exact (ENNReal.tendsto_toReal (measure_ne_top P _)).comp ht

/-- Natural truncations exhaust an extended cost, including infinity. -/
theorem iSup_min_nat (x : ℝ≥0∞) : (⨆ m : ℕ, min x (m : ℝ≥0∞)) = x := by
  rcases eq_top_or_lt_top x with rfl | hx
  · simpa only [min_eq_right le_top] using ENNReal.iSup_natCast
  · obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ne_of_lt hx)
    apply le_antisymm (iSup_le fun _ => min_le_left _ _)
    exact le_iSup_of_le m (by rw [min_eq_left hm.le])

/-- Monotone convergence is expressed in the extended nonnegative reals. -/
theorem expected_truncations (P : Measure X) (c : X → ℝ≥0∞) (hc : Measurable c) :
    (⨆ m : ℕ, ∫⁻ x, min (c x) (m : ℝ≥0∞) ∂P) = ∫⁻ x, c x ∂P := by
  rw [← lintegral_iSup (fun m => hc.min measurable_const)
    (fun a b hab x => min_le_min_left _ (Nat.cast_le.mpr hab))]
  simp_rw [iSup_min_nat]

/-- The decision limits and finite-record data processing use each input's own
law, while the accumulated cost is charged to the first input. -/
theorem terminal_klDiv_le
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (T : X → ℕ∞) (D : X → Fin 2) (hT : Measurable T)
    (Y : ℕ → Type*) [∀ m, MeasurableSpace (Y m)]
    (μ ν : ∀ m, Measure (Y m)) [∀ m, IsProbabilityMeasure (μ m)]
    [∀ m, IsProbabilityMeasure (ν m)]
    (A : ∀ m, Set (Y m)) (hA : ∀ m, MeasurableSet (A m)) (j : Fin 2)
    (hμ : ∀ m, μ m (A m) = P (truncatedDecisionEvent T D j m))
    (hν : ∀ m, ν m (A m) = Q (truncatedDecisionEvent T D j m))
    (hTP : ∀ᵐ x ∂P, T x ≠ ⊤) (hTQ : ∀ᵐ x ∂Q, T x ≠ ⊤)
    (L : ℝ≥0∞)
    (hprefix : ∀ m, klDiv (μ m) (ν m) ≤
      L * ∫⁻ x, min (ENat.toENNReal (T x)) (m : ℝ≥0∞) ∂P) :
    klDiv (binaryMeasure ⟨P.real {x | D x = j}, measureReal_nonneg, measureReal_le_one⟩)
      (binaryMeasure ⟨Q.real {x | D x = j}, measureReal_nonneg, measureReal_le_one⟩) ≤
        L * ∫⁻ x, ENat.toENNReal (T x) ∂P := by
  let p : ℕ → Icc (0 : ℝ) 1 := fun m =>
    ⟨(μ m).real (A m), measureReal_nonneg, measureReal_le_one⟩
  let q : ℕ → Icc (0 : ℝ) 1 := fun m =>
    ⟨(ν m).real (A m), measureReal_nonneg, measureReal_le_one⟩
  have hp : Tendsto p atTop (𝓝 ⟨P.real {x | D x = j}, measureReal_nonneg, measureReal_le_one⟩) := by
    apply tendsto_subtype_rng.mpr
    simpa only [p, Measure.real, hμ] using truncatedDecisionEvent_probability_tendsto P T D hTP j
  have hq : Tendsto q atTop (𝓝 ⟨Q.real {x | D x = j}, measureReal_nonneg, measureReal_le_one⟩) := by
    apply tendsto_subtype_rng.mpr
    simpa only [q, Measure.real, hν] using truncatedDecisionEvent_probability_tendsto Q T D hTQ j
  have hc : Measurable (fun x => ENat.toENNReal (T x)) :=
    (measurable_of_countable ENat.toENNReal).comp hT
  refine (binary_klDiv_le_liminf p q _ _ hp hq).trans ?_
  apply liminf_le_of_le (by isBoundedDefault)
  intro b hb
  obtain ⟨m, hm⟩ := hb.exists
  apply hm.trans
  refine (binary_klDiv_event_le (μ m) (ν m) (A m) (hA m)).trans ((hprefix m).trans ?_)
  rw [← expected_truncations P _ hc]
  exact mul_le_mul' le_rfl (le_iSup (fun m : ℕ =>
    ∫⁻ x, min (ENat.toENNReal (T x)) (m : ℝ≥0∞) ∂P) m)

/-- Exact sequential testing information for every confidence in (0,1/2).
In particular, no uniform logarithmic comparison is asserted at delta=1/2. -/
theorem information_of_errors
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (T : X → ℕ∞) (D : X → Fin 2) (hT : Measurable T) (hD : Measurable D)
    (Y : ℕ → Type*) [∀ m, MeasurableSpace (Y m)]
    (μ ν : ∀ m, Measure (Y m)) [∀ m, IsProbabilityMeasure (μ m)]
    [∀ m, IsProbabilityMeasure (ν m)]
    (A : ∀ m, Set (Y m)) (hA : ∀ m, MeasurableSet (A m)) (j : Fin 2)
    (hμ : ∀ m, μ m (A m) = P (truncatedDecisionEvent T D j m))
    (hν : ∀ m, ν m (A m) = Q (truncatedDecisionEvent T D j m))
    (hTP : ∀ᵐ x ∂P, T x ≠ ⊤) (hTQ : ∀ᵐ x ∂Q, T x ≠ ⊤)
    (L : ℝ≥0∞)
    (hprefix : ∀ m, klDiv (μ m) (ν m) ≤
      L * ∫⁻ x, min (ENat.toENNReal (T x)) (m : ℝ≥0∞) ∂P)
    (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (heP : P {x | D x ≠ j} ≤ ENNReal.ofReal δ)
    (heQ : Q {x | D x = j} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * ∫⁻ x, ENat.toENNReal (T x) ∂P := by
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top heP
  have hq := ENNReal.toReal_mono ENNReal.ofReal_ne_top heQ
  rw [ENNReal.toReal_ofReal hδ.le] at he hq
  have hc := probReal_compl_eq_one_sub (μ := P) (hD (measurableSet_singleton j))
  change P.real ({x | D x = j}ᶜ) = 1 - P.real {x | D x = j} at hc
  have hp : 1 - δ ≤ P.real {x | D x = j} := by
    change P.real ({x | D x = j}ᶜ) ≤ δ at he
    rw [hc] at he
    linarith
  exact (testingThreshold_le_binary_klDiv_via_derivatives δ hδ hhalf _ _ hp hq).trans
    (terminal_klDiv_le P Q T D hT Y μ ν A hA j hμ hν hTP hTQ L hprefix)

end LocalCertification.Information.KernelTerminal
