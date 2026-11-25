import LocalCertification.Information.FiniteAtoms

/- Joint relative entropy over an arbitrary measurable history space under almost-everywhere absolute continuity. No standard Borel assumption on histories is needed. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
namespace LocalCertification.Information
universe u v
variable {O : Type u} [MeasurableSpace O] [Fintype O] [MeasurableSingletonClass O]
variable {H : Type v} [MeasurableSpace H]
  (κ η : Kernel H O) [IsMarkovKernel κ] [IsMarkovKernel η]

def jointDensity (p : H × O) : ℝ≥0∞ :=
  atomDensity (κ p.1) (η p.1) p.2

omit [IsMarkovKernel κ] [IsMarkovKernel η] in
theorem measurable_jointDensity : Measurable (jointDensity κ η) := by
  apply measurable_from_prod_countable_left
  intro o
  unfold jointDensity atomDensity
  exact (((κ.measurable_coe (measurableSet_singleton o)).ennreal_toReal.div
    (η.measurable_coe (measurableSet_singleton o)).ennreal_toReal)).ennreal_ofReal

omit [IsMarkovKernel κ] [IsMarkovKernel η] in
theorem measurable_atomKLSum :
    Measurable (fun h : H => ∑ o : O, atomKL (κ h) (η h) o) := by
  apply Finset.measurable_sum
  intro o _
  unfold atomKL
  exact (η.measurable_coe (measurableSet_singleton o)).mul
    (measurable_klFun.comp
      ((κ.measurable_coe (measurableSet_singleton o)).ennreal_toReal.div
        (η.measurable_coe (measurableSet_singleton o)).ennreal_toReal)).ennreal_ofReal

theorem joint_withDensity (μ : Measure H) [IsFiniteMeasure μ]
    (hAC : ∀ᵐ h ∂μ, κ h ≪ η h) :
    (μ ⊗ₘ η).withDensity (jointDensity κ η) = μ ⊗ₘ κ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_jointDensity κ η) hf,
    Measure.lintegral_compProd ((measurable_jointDensity κ η).mul hf),
    Measure.lintegral_compProd hf]
  apply lintegral_congr_ae
  filter_upwards [hAC] with h hh
  rw [lintegral_fintype, lintegral_fintype]
  apply Finset.sum_congr rfl
  intro o _
  change (atomDensity (κ h) (η h) o * f (h, o)) * η h {o} =
    f (h, o) * κ h {o}
  calc
    (atomDensity (κ h) (η h) o * f (h, o)) * η h {o} =
        f (h, o) * (atomDensity (κ h) (η h) o * η h {o}) := by ac_rfl
    _ = f (h, o) * κ h {o} := by rw [atomDensity_mul hh]

theorem joint_klDiv_eq_lintegral_sum (μ : Measure H) [IsFiniteMeasure μ]
    (hAC : ∀ᵐ h ∂μ, κ h ≪ η h) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) =
      ∫⁻ h, ∑ o : O, atomKL (κ h) (η h) o ∂μ := by
  have hJoint : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right hAC
  have hrn := Measure.rnDeriv_withDensity (μ ⊗ₘ η)
    (measurable_jointDensity κ η)
  rw [joint_withDensity κ η μ hAC] at hrn
  rw [klDiv_eq_lintegral_klFun_of_ac hJoint]
  calc
    (∫⁻ p, ENNReal.ofReal
        (klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)) p).toReal) ∂(μ ⊗ₘ η)) =
      ∫⁻ p, ENNReal.ofReal (klFun (jointDensity κ η p).toReal) ∂(μ ⊗ₘ η) := by
        apply lintegral_congr_ae
        filter_upwards [hrn] with p hp
        rw [hp]
    _ = ∫⁻ h, ∑ o : O, atomKL (κ h) (η h) o ∂μ := by
      have hm : Measurable (fun p => ENNReal.ofReal
          (klFun (jointDensity κ η p).toReal)) :=
        (measurable_klFun.comp
          (measurable_jointDensity κ η).ennreal_toReal).ennreal_ofReal
      rw [Measure.lintegral_compProd (μ := μ) (κ := η) hm]
      apply lintegral_congr
      intro h
      rw [lintegral_fintype]
      apply Finset.sum_congr rfl
      intro o _
      simp only [jointDensity, atomDensity, atomKL,
        ENNReal.toReal_ofReal
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
        mul_comm]

theorem joint_klDiv_eq_lintegral (μ : Measure H) [IsFiniteMeasure μ]
    (hAC : ∀ᵐ h ∂μ, κ h ≪ η h) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ h, klDiv (κ h) (η h) ∂μ := by
  rw [joint_klDiv_eq_lintegral_sum κ η μ hAC]
  apply lintegral_congr_ae
  filter_upwards [hAC] with h hh
  exact (finite_klDiv_eq_sum hh).symm

theorem aemeasurable_conditionalKL (μ : Measure H) [IsFiniteMeasure μ]
    (hAC : ∀ᵐ h ∂μ, κ h ≪ η h) :
    AEMeasurable (fun h => klDiv (κ h) (η h)) μ := by
  apply (measurable_atomKLSum κ η).aemeasurable.congr
  filter_upwards [hAC] with h hh
  exact (finite_klDiv_eq_sum hh).symm

theorem joint_klDiv_le (μ : Measure H) [IsProbabilityMeasure μ]
    (hAC : ∀ᵐ h ∂μ, κ h ≪ η h) (L : ℝ≥0∞)
    (hL : ∀ᵐ h ∂μ, klDiv (κ h) (η h) ≤ L) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≤ L := by
  rw [joint_klDiv_eq_lintegral κ η μ hAC]
  calc
    (∫⁻ h, klDiv (κ h) (η h) ∂μ) ≤ ∫⁻ _ : H, L ∂μ :=
      lintegral_mono_ae hL
    _ = L := by simp

end LocalCertification.Information
