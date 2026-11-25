import LocalCertification.Information.BinarySupport
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
open MeasureTheory InformationTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
namespace LocalCertification.Information

/-- The full finite-atom perspective is the supremum of its actual exponential supports.
This includes zero source, zero denominator and the singular infinite value. -/
theorem atomPerspective_eq_iSup_support {O : Type*} [MeasurableSpace O]
    (P Q : Measure O) [IsFiniteMeasure P] [IsFiniteMeasure Q] (o : O) :
    atomPerspective P Q o = ⨆ t : ℝ,
      ENNReal.ofReal (t * (P {o}).toReal - (Real.exp t - 1) * (Q {o}).toReal) := by
  classical
  apply le_antisymm
  · by_cases hQ : Q {o} = 0
    · by_cases hP : P {o} = 0
      · simp [atomPerspective, hQ, hP]
      · rw [atomPerspective, ite_eq_left hQ, ite_eq_right hP]
        apply top_le_iff.mpr
        apply ENNReal.eq_top_of_forall_nnreal_le
        intro r
        have ha : 0 < (P {o}).toReal := ENNReal.toReal_pos hP (measure_ne_top P {o})
        have he : ENNReal.ofReal (((r : ℝ) / (P {o}).toReal) * (P {o}).toReal -
            (Real.exp ((r : ℝ) / (P {o}).toReal) - 1) * (Q {o}).toReal) = r := by
          simp [hQ, div_mul_cancel₀ _ ha.ne']
        exact he ▸ le_iSup (fun t : ℝ => ENNReal.ofReal
          (t * (P {o}).toReal - (Real.exp t - 1) * (Q {o}).toReal))
          ((r : ℝ) / (P {o}).toReal)
    · have hb : 0 < (Q {o}).toReal := ENNReal.toReal_pos hQ (measure_ne_top Q {o})
      rw [atomPerspective, ite_eq_right hQ, atomKL]
      by_cases hP : P {o} = 0
      · simp only [hP, ENNReal.toReal_zero, zero_div, klFun_zero, ENNReal.ofReal_one, mul_one]
        have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal
            (t * (P {o}).toReal - (Real.exp t - 1) * (Q {o}).toReal)) atBot
            (𝓝 (Q {o})) := by
          simp only [hP, ENNReal.toReal_zero, mul_zero, zero_sub]
          have he := ((Real.tendsto_exp_atBot.sub_const 1).mul_const (Q {o}).toReal).neg
          have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
          convert hh using 1 <;> first | rfl | simp only [zero_sub, neg_one_mul, neg_neg,
            ENNReal.ofReal_toReal (measure_ne_top Q {o})]
        apply le_of_tendsto hlim
        apply Eventually.of_forall
        intro t
        simpa only [hP, ENNReal.toReal_zero] using
          (le_iSup (fun t : ℝ => ENNReal.ofReal
            (t * (P {o}).toReal - (Real.exp t - 1) * (Q {o}).toReal)) t)
      · have ha : 0 < (P {o}).toReal := ENNReal.toReal_pos hP (measure_ne_top P {o})
        have he : ENNReal.ofReal (Real.log ((P {o}).toReal / (Q {o}).toReal) *
            (P {o}).toReal - (Real.exp (Real.log ((P {o}).toReal / (Q {o}).toReal)) - 1) *
            (Q {o}).toReal) = Q {o} * ENNReal.ofReal
            (klFun ((P {o}).toReal / (Q {o}).toReal)) := by
          calc
            _ = ENNReal.ofReal ((Q {o}).toReal *
                klFun ((P {o}).toReal / (Q {o}).toReal)) := by
              congr 1
              rw [Real.exp_log (div_pos ha hb), klFun_apply]
              field_simp
              ring
            _ = _ := by rw [ENNReal.ofReal_mul hb.le,
              ENNReal.ofReal_toReal (measure_ne_top Q {o})]
        exact he ▸ le_iSup (fun t : ℝ => ENNReal.ofReal
          (t * (P {o}).toReal - (Real.exp t - 1) * (Q {o}).toReal))
          (Real.log ((P {o}).toReal / (Q {o}).toReal))
  · exact iSup_le (fun t => exponential_support_le_atomPerspective P Q o t)

/-- Full atom perspectives vary lower semicontinuously whenever their real masses are continuous.
No absolute continuity or positive-denominator condition is imposed. -/
theorem lowerSemicontinuous_atomPerspective {X O : Type*} [TopologicalSpace X]
    [MeasurableSpace O] (P Q : X → Measure O)
    [∀ x, IsFiniteMeasure (P x)] [∀ x, IsFiniteMeasure (Q x)] (o : O)
    (hp : Continuous (fun x => (P x {o}).toReal))
    (hq : Continuous (fun x => (Q x {o}).toReal)) :
    LowerSemicontinuous (fun x => atomPerspective (P x) (Q x) o) := by
  simp_rw [atomPerspective_eq_iSup_support]
  apply lowerSemicontinuous_iSup
  intro t
  exact (ENNReal.continuous_ofReal.comp
    ((continuous_const.mul hp).sub (continuous_const.mul hq))).lowerSemicontinuous

/-- Finite-outcome KL is lower semicontinuous in all atom masses, including singular limits. -/
theorem lowerSemicontinuous_finite_klDiv {X O : Type*} [TopologicalSpace X]
    [MeasurableSpace O] [Fintype O] [MeasurableSingletonClass O] (P Q : X → Measure O)
    [∀ x, IsFiniteMeasure (P x)] [∀ x, IsFiniteMeasure (Q x)]
    (hp : ∀ o, Continuous (fun x => (P x {o}).toReal))
    (hq : ∀ o, Continuous (fun x => (Q x {o}).toReal)) :
    LowerSemicontinuous (fun x => klDiv (P x) (Q x)) := by
  classical
  simp_rw [finite_klDiv_eq_sum_perspective]
  have hs (s : Finset O) : LowerSemicontinuous
      (fun x => ∑ o ∈ s, atomPerspective (P x) (Q x) o) := by
    induction s using Finset.induction_on with
    | empty => simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : X => (0 : ℝ≥0∞)))
    | @insert o s ho ih =>
      simpa only [Finset.sum_insert ho] using
        (lowerSemicontinuous_atomPerspective P Q o (hp o) (hq o)).add ih
  exact hs Finset.univ


/-- The actual binary probability measure, with parameter in the closed unit interval. -/
def binaryMeasure (p : Icc (0 : ℝ) 1) : Measure (Fin 2) :=
  ENNReal.ofReal (p : ℝ) • Measure.dirac 0 +
    ENNReal.ofReal (1 - (p : ℝ)) • Measure.dirac 1

instance binaryMeasure_probability (p : Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (binaryMeasure p) := by
  constructor
  simp only [binaryMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add p.property.1 (sub_nonneg.mpr p.property.2)]
  simp

@[simp] theorem binaryMeasure_zero (p : Icc (0 : ℝ) 1) :
    binaryMeasure p {0} = ENNReal.ofReal (p : ℝ) := by
  simp [binaryMeasure]

@[simp] theorem binaryMeasure_one (p : Icc (0 : ℝ) 1) :
    binaryMeasure p {1} = ENNReal.ofReal (1 - (p : ℝ)) := by
  simp [binaryMeasure]

@[simp] theorem binaryMeasure_real_zero (p : Icc (0 : ℝ) 1) :
    (binaryMeasure p {0}).toReal = (p : ℝ) := by
  rw [binaryMeasure_zero, ENNReal.toReal_ofReal p.property.1]

@[simp] theorem binaryMeasure_real_one (p : Icc (0 : ℝ) 1) :
    (binaryMeasure p {1}).toReal = 1 - (p : ℝ) := by
  rw [binaryMeasure_one, ENNReal.toReal_ofReal (sub_nonneg.mpr p.property.2)]

/-- Joint lower semicontinuity of actual binary KL on the entire closed probability square. -/
theorem lowerSemicontinuous_binary_klDiv :
    LowerSemicontinuous (fun z : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
      klDiv (binaryMeasure z.1) (binaryMeasure z.2)) := by
  apply lowerSemicontinuous_finite_klDiv
  · intro o
    fin_cases o
    · change Continuous (fun x : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
        (binaryMeasure x.1 {0}).toReal)
      simp only [binaryMeasure_real_zero]
      fun_prop
    · change Continuous (fun x : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
        (binaryMeasure x.1 {1}).toReal)
      simp only [binaryMeasure_real_one]
      fun_prop
  · intro o
    fin_cases o
    · change Continuous (fun x : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
        (binaryMeasure x.2 {0}).toReal)
      simp only [binaryMeasure_real_zero]
      fun_prop
    · change Continuous (fun x : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
        (binaryMeasure x.2 {1}).toReal)
      simp only [binaryMeasure_real_one]
      fun_prop

/-- Full binary KL obeys the lower-limit inequality along any convergent probability pairs. -/
theorem binary_klDiv_le_liminf {ι : Type*} {l : Filter ι} [l.NeBot]
    (p q : ι → Icc (0 : ℝ) 1) (p₀ q₀ : Icc (0 : ℝ) 1)
    (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) :
    klDiv (binaryMeasure p₀) (binaryMeasure q₀) ≤
      liminf (fun i => klDiv (binaryMeasure (p i)) (binaryMeasure (q i))) l := by
  apply le_of_forall_lt
  intro r hr
  obtain ⟨s, hrs, hs⟩ := exists_between hr
  apply hrs.trans_le
  apply le_liminf_of_le (by isBoundedDefault)
  exact ((hp.prodMk_nhds hq).eventually
    (lowerSemicontinuous_binary_klDiv (p₀, q₀) s hs)).mono (fun _ h => h.le)

/-- Positive source acceptance over zero target acceptance retains infinite KL. -/
theorem binary_klDiv_target_zero (p q : Icc (0 : ℝ) 1)
    (hp : 0 < (p : ℝ)) (hq : (q : ℝ) = 0) :
    klDiv (binaryMeasure p) (binaryMeasure q) = ∞ := by
  apply klDiv_of_not_ac
  intro h
  have hzero : binaryMeasure q {0} = 0 := by simp [hq]
  have hpos : binaryMeasure p {0} ≠ 0 := by
    rw [binaryMeasure_zero]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  exact hpos (h hzero)

/-- Positive source rejection over zero target rejection also retains infinite KL. -/
theorem binary_klDiv_target_one (p q : Icc (0 : ℝ) 1)
    (hp : (p : ℝ) < 1) (hq : (q : ℝ) = 1) :
    klDiv (binaryMeasure p) (binaryMeasure q) = ∞ := by
  apply klDiv_of_not_ac
  intro h
  have hzero : binaryMeasure q {1} = 0 := by simp [hq]
  have hpos : binaryMeasure p {1} ≠ 0 := by
    rw [binaryMeasure_one]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp))
  exact hpos (h hzero)


/-- The standard binary logarithmic formula, valid for every source probability when the
reference probability is interior; endpoint source terms use the established `0 log 0 = 0`. -/
theorem binary_klDiv_formula (p q : Icc (0 : ℝ) 1)
    (hq₀ : 0 < (q : ℝ)) (hq₁ : (q : ℝ) < 1) :
    klDiv (binaryMeasure p) (binaryMeasure q) = ENNReal.ofReal
      ((p : ℝ) * Real.log ((p : ℝ) / (q : ℝ)) +
        (1 - (p : ℝ)) * Real.log ((1 - (p : ℝ)) / (1 - (q : ℝ)))) := by
  have hq₂ : 0 < 1 - (q : ℝ) := sub_pos.mpr hq₁
  have hzero : binaryMeasure q {0} ≠ 0 := by
    rw [binaryMeasure_zero]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hq₀)
  have hone : binaryMeasure q {1} ≠ 0 := by
    rw [binaryMeasure_one]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hq₂)
  rw [finite_klDiv_eq_sum_perspective, Fin.sum_univ_two]
  simp only [atomPerspective]
  rw [ite_eq_right hzero, ite_eq_right hone]
  simp only [atomKL]
  rw [binaryMeasure_real_zero, binaryMeasure_real_zero, binaryMeasure_real_one,
    binaryMeasure_real_one, binaryMeasure_zero, binaryMeasure_one]
  rw [← ENNReal.ofReal_mul hq₀.le, ← ENNReal.ofReal_mul hq₂.le,
    ← ENNReal.ofReal_add
      (mul_nonneg hq₀.le (klFun_nonneg (div_nonneg p.property.1 hq₀.le)))
      (mul_nonneg hq₂.le (klFun_nonneg (div_nonneg (sub_nonneg.mpr p.property.2) hq₂.le)))]
  congr 1
  simp only [klFun_apply]
  field_simp
  ring

/-- The actual indicator decision, keeping acceptance labelled zero. -/
def binaryDecision {X : Type*} (A : Set X) : X → Fin 2 := by
  classical
  exact fun x => if x ∈ A then 0 else 1

/-- A measurable binary decision has exactly the measure above, on any original measurable space. -/
theorem binaryMeasure_event {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (A : Set X) (hA : MeasurableSet A) :
    P.map (binaryDecision A) =
      binaryMeasure ⟨P.real A, measureReal_nonneg, measureReal_le_one⟩ := by
  classical
  let f : X → Fin 2 := fun x => if x ∈ A then 0 else 1
  have hf : Measurable f := Measurable.ite hA measurable_const measurable_const
  have hzero : f ⁻¹' ({0} : Set (Fin 2)) = A := by ext x; simp [f]
  have hone : f ⁻¹' ({1} : Set (Fin 2)) = Aᶜ := by ext x; simp [f]
  let p : Icc (0 : ℝ) 1 := ⟨P.real A, measureReal_nonneg, measureReal_le_one⟩
  change P.map f = binaryMeasure p
  apply Measure.ext_of_singleton
  intro o
  fin_cases o
  · change P.map f {0} = binaryMeasure p {0}
    rw [Measure.map_apply hf (measurableSet_singleton _), hzero, binaryMeasure_zero]
    exact (ENNReal.ofReal_toReal (measure_ne_top P A)).symm
  · change P.map f {1} = binaryMeasure p {1}
    rw [Measure.map_apply hf (measurableSet_singleton _), hone, binaryMeasure_one]
    change P Aᶜ = ENNReal.ofReal (1 - P.real A)
    rw [← probReal_compl_eq_one_sub hA]
    exact (ENNReal.ofReal_toReal (measure_ne_top P Aᶜ)).symm

/-- Binary data processing is instantiated by the genuine original decision laws. -/
theorem binary_klDiv_event_le {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set X) (hA : MeasurableSet A) :
    klDiv (binaryMeasure ⟨P.real A, measureReal_nonneg, measureReal_le_one⟩)
      (binaryMeasure ⟨Q.real A, measureReal_nonneg, measureReal_le_one⟩) ≤ klDiv P Q := by
  rw [← binaryMeasure_event P A hA, ← binaryMeasure_event Q A hA]
  exact klDiv_map_le P Q (Measurable.ite hA measurable_const measurable_const)


/-- Zero-source boundary of binary KL for an interior reference. -/
theorem binary_klDiv_source_zero (q : Icc (0 : ℝ) 1)
    (hq₀ : 0 < (q : ℝ)) (hq₁ : (q : ℝ) < 1) :
    klDiv (binaryMeasure 0) (binaryMeasure q) = ENNReal.ofReal (-Real.log (1 - (q : ℝ))) := by
  rw [binary_klDiv_formula _ _ hq₀ hq₁]
  congr 1
  simp [div_eq_mul_inv]

/-- Unit-source boundary of binary KL for an interior reference. -/
theorem binary_klDiv_source_one (q : Icc (0 : ℝ) 1)
    (hq₀ : 0 < (q : ℝ)) (hq₁ : (q : ℝ) < 1) :
    klDiv (binaryMeasure 1) (binaryMeasure q) = ENNReal.ofReal (-Real.log (q : ℝ)) := by
  rw [binary_klDiv_formula _ _ hq₀ hq₁]
  congr 1
  simp [div_eq_mul_inv]

namespace Consumers

/-- All four corner cases retain the exact zero or singular-infinite value. -/
theorem binary_corner_values :
    klDiv (binaryMeasure 0) (binaryMeasure 0) = 0 ∧
    klDiv (binaryMeasure 1) (binaryMeasure 1) = 0 ∧
    klDiv (binaryMeasure 0) (binaryMeasure 1) = ∞ ∧
    klDiv (binaryMeasure 1) (binaryMeasure 0) = ∞ := by
  refine ⟨klDiv_self _, klDiv_self _, ?_, ?_⟩
  · exact binary_klDiv_target_one 0 1 (by norm_num) (by norm_num)
  · exact binary_klDiv_target_zero 1 0 (by norm_num) (by norm_num)

/-- Concrete nonconstant interior reference probabilities tending to the singular boundary. -/
def shrinkingBinaryReference (n : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨1 / ((n : ℝ) + 2), by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩

theorem shrinkingBinaryReference_interior (n : ℕ) :
    0 < (shrinkingBinaryReference n : ℝ) ∧ (shrinkingBinaryReference n : ℝ) < 1 := by
  change 0 < 1 / ((n : ℝ) + 2) ∧ 1 / ((n : ℝ) + 2) < 1
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem shrinkingBinaryReference_tendsto :
    Tendsto shrinkingBinaryReference atTop (𝓝 (0 : Icc (0 : ℝ) 1)) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    ((tendsto_add_atTop_iff_nat 2).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- Every KL in this genuine binary sequence is finite, while its lower limit is infinite.
The positive source is arbitrary, including the deterministic source at one. -/
theorem binary_finite_sequence_singular_limit (p : Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ)) :
    (∀ n, klDiv (binaryMeasure p) (binaryMeasure (shrinkingBinaryReference n)) ≠ ∞) ∧
    liminf (fun n => klDiv (binaryMeasure p)
      (binaryMeasure (shrinkingBinaryReference n))) atTop = ∞ := by
  constructor
  · intro n
    rw [binary_klDiv_formula p _ (shrinkingBinaryReference_interior n).1
      (shrinkingBinaryReference_interior n).2]
    exact ENNReal.ofReal_ne_top
  · apply top_le_iff.mp
    have h := binary_klDiv_le_liminf (fun _ : ℕ => p) shrinkingBinaryReference p 0
      tendsto_const_nhds shrinkingBinaryReference_tendsto
    rwa [binary_klDiv_target_zero p 0 hp (by norm_num)] at h

end Consumers
end LocalCertification.Information
