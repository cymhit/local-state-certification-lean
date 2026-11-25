import LocalCertification.Information.JointFiniteKL

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Information

variable {O : Type*} [MeasurableSpace O] [Fintype O] [MeasurableSingletonClass O]

omit [MeasurableSingletonClass O] in
/-- Finite-space absolute continuity is precisely the absence of positive source mass on null atoms. -/
theorem finite_absolutelyContinuous_iff_atoms (P Q : Measure O) :
    P ≪ Q ↔ ∀ o, Q {o} = 0 → P {o} = 0 := by
  classical
  refine ⟨fun h o ho => h ho, ?_⟩
  intro h s hs
  have he : s = ⋃ o : O, if o ∈ s then ({o} : Set O) else ∅ := by ext x; simp
  rw [he]
  apply measure_iUnion_null
  intro o
  split_ifs with ho
  · exact h o (measure_mono_null (Set.singleton_subset_iff.mpr ho) hs)
  · simp

/-- Full nonnegative perspective: a positive source atom over a zero denominator contributes infinity. -/
def atomPerspective (P Q : Measure O) (o : O) : ℝ≥0∞ :=
  if Q {o} = 0 then if P {o} = 0 then 0 else ∞ else atomKL P Q o

omit [Fintype O] [MeasurableSingletonClass O] in
theorem atomPerspective_eq_atomKL_of_ac {P Q : Measure O} (h : P ≪ Q) (o : O) :
    atomPerspective P Q o = atomKL P Q o := by
  classical
  by_cases hQ : Q {o} = 0
  · simp [atomPerspective,atomKL,hQ,h hQ]
  · simp [atomPerspective,hQ]

/-- The finite measure formula has no absolute-continuity or finite-KL hypothesis. -/
theorem finite_klDiv_eq_sum_perspective (P Q : Measure O) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    klDiv P Q = ∑ o, atomPerspective P Q o := by
  classical
  by_cases h : P ≪ Q
  · rw [finite_klDiv_eq_sum h]
    exact Finset.sum_congr rfl (fun o _ => (atomPerspective_eq_atomKL_of_ac h o).symm)
  · rw [klDiv_of_not_ac h]
    have hx : ¬ ∀ o, Q {o} = 0 → P {o} = 0 := (finite_absolutelyContinuous_iff_atoms P Q).not.mp h
    push Not at hx
    obtain ⟨o,hQ,hP⟩ := hx
    apply Eq.symm
    apply top_unique
    calc
      ∞ = atomPerspective P Q o := by simp [atomPerspective,hQ,hP]
      _ ≤ ∑ x, atomPerspective P Q x := Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ o)

variable {H : Type*} [MeasurableSpace H]
    (κ η : Kernel H O) [IsMarkovKernel κ] [IsMarkovKernel η]

/-- Joint AC is equivalent to conditional AC a.e.; history remains an arbitrary measurable space. -/
theorem joint_absolutelyContinuous_iff (μ : Measure H) [IsFiniteMeasure μ] :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η ↔ ∀ᵐ h ∂μ, κ h ≪ η h := by
  constructor
  · intro hAC
    have hatom (o : O) : ∀ᵐ h ∂μ, η h {o} = 0 → κ h {o} = 0 := by
      let s := {h : H | η h {o} = 0}
      have hs : MeasurableSet s := measurableSet_eq_fun (η.measurable_coe (measurableSet_singleton o)) measurable_const
      have hz : (μ ⊗ₘ η) (s ×ˢ ({o} : Set O)) = 0 := by
        rw [Measure.compProd_apply_prod hs (measurableSet_singleton o)]
        exact (setLIntegral_eq_zero_iff hs (η.measurable_coe (measurableSet_singleton o))).mpr
          (Filter.Eventually.of_forall fun h hh => hh)
      have hp := hAC hz
      rw [Measure.compProd_apply_prod hs (measurableSet_singleton o)] at hp
      exact (setLIntegral_eq_zero_iff hs (κ.measurable_coe (measurableSet_singleton o))).mp hp
    have hall := Filter.eventually_all.mpr hatom
    filter_upwards [hall] with h hh
    exact (finite_absolutelyContinuous_iff_atoms _ _).mpr hh
  · exact Measure.AbsolutelyContinuous.compProd_right

omit [IsMarkovKernel κ] [IsMarkovKernel η] [Fintype O] in
theorem measurable_atomPerspective (o : O) : Measurable (fun h => atomPerspective (κ h) (η h) o) := by
  classical
  have hp := κ.measurable_coe (measurableSet_singleton o)
  have hq := η.measurable_coe (measurableSet_singleton o)
  unfold atomPerspective
  apply Measurable.ite (measurableSet_eq_fun hq measurable_const)
  · exact Measurable.ite (measurableSet_eq_fun hp measurable_const) measurable_const measurable_const
  · exact hq.mul ((measurable_klFun.comp (hp.ennreal_toReal.div hq.ennreal_toReal)).ennreal_ofReal)

/-- Conditional KL is genuinely measurable, including infinity on singular histories. -/
theorem measurable_conditionalKL_full : Measurable (fun h => klDiv (κ h) (η h)) := by
  simp_rw [finite_klDiv_eq_sum_perspective]
  exact Finset.measurable_sum _ (fun o _ => measurable_atomPerspective κ η o)

/-- Complete finite-observation chain integral, including arbitrary singular histories and infinite KL. -/
theorem joint_klDiv_eq_lintegral_full (μ : Measure H) [IsFiniteMeasure μ] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ h, klDiv (κ h) (η h) ∂μ := by
  by_cases hAC : ∀ᵐ h ∂μ, κ h ≪ η h
  · exact joint_klDiv_eq_lintegral κ η μ hAC
  · rw [klDiv_of_not_ac ((joint_absolutelyContinuous_iff κ η μ).not.mpr hAC)]
    apply Eq.symm
    by_contra hfin
    apply hAC
    filter_upwards [ae_lt_top (measurable_conditionalKL_full κ η) hfin] with h hh
    by_contra hnot
    rw [klDiv_of_not_ac hnot] at hh
    exact (lt_irrefl ∞) hh

/-- The full nonnegative perspective formula K, with both zero/zero and positive/zero branches explicit. -/
theorem joint_klDiv_eq_lintegral_perspective (μ : Measure H) [IsFiniteMeasure μ] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ h, ∑ o, atomPerspective (κ h) (η h) o ∂μ := by
  rw [joint_klDiv_eq_lintegral_full]
  simp_rw [finite_klDiv_eq_sum_perspective]

end LocalCertification.Information
