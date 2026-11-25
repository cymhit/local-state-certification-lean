import LocalCertification.Quantum.MeasurablePOVM
import LocalCertification.Quantum.BornMeasure
import QIT.Core.POVMProbability
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite POVMs as matrix measures

The counting-measure density of a finite QIT POVM is a genuine measurable
POVM. Each original effect and Born probability is preserved. In particular,
this construction does not require projective or rank-one effects.
-/

set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

namespace LocalCertification.Quantum.MeasurablePOVM

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype Ω] [MeasurableSingletonClass Ω]
  [Fintype I] [DecidableEq I]

private theorem effects_setIntegral (M : QIT.POVM Ω I) (A : Set Ω) (hA : MeasurableSet A) :
    ∫ x in A, M.effects x ∂Measure.count = ∑ x, A.indicator M.effects x := by
  rw [← integral_indicator hA, integral_count]

/-- The finite POVM embedded by its effects as a density against counting measure. -/
def ofFinite (M : QIT.POVM Ω I) : MeasurablePOVM Ω I where
  toVectorMeasure := Measure.count.withDensityᵥ M.effects
  positive A hA := by
    rw [withDensityᵥ_apply Integrable.of_finite hA, effects_setIntegral M A hA]
    apply Matrix.nonneg_iff_posSemidef.mp
    apply Finset.sum_nonneg
    intro x _
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx] using (M.pos x).nonneg
    · simp [hx]
  univ := by
    rw [withDensityᵥ_apply Integrable.of_finite MeasurableSet.univ]
    simp [M.sum_eq_one]

theorem ofFinite_apply (M : QIT.POVM Ω I) {A : Set Ω} (hA : MeasurableSet A) :
    (ofFinite M).toVectorMeasure A = ∑ x, A.indicator M.effects x := by
  rw [ofFinite, withDensityᵥ_apply Integrable.of_finite hA, effects_setIntegral M A hA]

@[simp] theorem ofFinite_singleton (M : QIT.POVM Ω I) (x : Ω) :
    (ofFinite M).toVectorMeasure {x} = M.effects x := by
  classical
  rw [ofFinite_apply M (measurableSet_singleton x)]
  simp

@[simp] theorem born_ofFinite_singleton [DecidableEq Ω] (M : QIT.POVM Ω I) (ρ : QIT.State I) (x : Ω) :
    (ofFinite M).born ρ {x} = (M.prob ρ x : ℝ≥0∞) := by
  rw [born_apply _ ρ (measurableSet_singleton x), ofFinite_singleton,
    ← M.prob_eq_trace_re ρ x]
  simp

/-- Embedding preserves the existing finite QIT Born measure on every measurable set. -/
theorem born_ofFinite [DecidableEq Ω] (M : QIT.POVM Ω I) (ρ : QIT.State I) :
    (ofFinite M).born ρ = LocalCertification.Quantum.povmBornMeasure M ρ := by
  apply Measure.ext_of_singleton
  intro x
  rw [born_ofFinite_singleton, LocalCertification.Quantum.povmBornMeasure_atom]

end LocalCertification.Quantum.MeasurablePOVM
