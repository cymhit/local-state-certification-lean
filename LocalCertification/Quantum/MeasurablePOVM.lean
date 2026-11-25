import QIT.States.Schatten
import Mathlib.MeasureTheory.VectorMeasure.Order
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# POVMs on arbitrary measurable outcome spaces

A finite-dimensional POVM is a countably additive positive matrix measure
whose total effect is the identity. Its Born probability and normalized trace
reference probability are constructed from positive scalar evaluations.
The outcome space has no finiteness or standard-Borel requirement.

This is the measurement layer used in Supplemental Material Sections I and IV.A.
-/

set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal ComplexOrder MatrixOrder
noncomputable section

namespace LocalCertification.Quantum

/-- A normalized positive matrix measure on an arbitrary measurable space. -/
structure MeasurablePOVM (Ω I : Type*) [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] where
  toVectorMeasure : VectorMeasure Ω (Matrix I I ℂ)
  positive : ∀ A, MeasurableSet A → (toVectorMeasure A).PosSemidef
  univ : toVectorMeasure Set.univ = 1

namespace MeasurablePOVM

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

private def positiveScalarMeasure (M : MeasurablePOVM Ω I)
    (f : Matrix I I ℂ →+ ℝ) (hf : Continuous f)
    (hpos : ∀ A, MeasurableSet A → 0 ≤ f (M.toVectorMeasure A)) : Measure Ω :=
  SignedMeasure.toMeasureOfZeroLE (M.toVectorMeasure.mapRange f hf) Set.univ MeasurableSet.univ
    ((VectorMeasure.le_restrict_univ_iff_le _ _).mpr (fun A hA => by
      simpa only [_root_.zero_apply, VectorMeasure.mapRange_apply] using hpos A hA))

private theorem positiveScalarMeasure_apply (M : MeasurablePOVM Ω I)
    (f : Matrix I I ℂ →+ ℝ) (hf : Continuous f)
    (hpos : ∀ A, MeasurableSet A → 0 ≤ f (M.toVectorMeasure A))
    {A : Set Ω} (hA : MeasurableSet A) :
    positiveScalarMeasure M f hf hpos A = ENNReal.ofReal (f (M.toVectorMeasure A)) := by
  rw [positiveScalarMeasure, SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hA]
  simp only [Set.univ_inter, VectorMeasure.mapRange_apply]
  exact (ENNReal.ofReal_eq_coe_nnreal _).symm

private def bornFunctional (ρ : QIT.State I) : Matrix I I ℂ →+ ℝ where
  toFun A := (ρ.matrix * A).trace.re
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add]

private theorem bornFunctional_continuous (ρ : QIT.State I) :
    Continuous (bornFunctional ρ) := by
  change Continuous (fun A : Matrix I I ℂ => (ρ.matrix * A).trace.re)
  fun_prop

private theorem bornFunctional_nonneg (M : MeasurablePOVM Ω I) (ρ : QIT.State I)
    (A : Set Ω) (hA : MeasurableSet A) : 0 ≤ bornFunctional ρ (M.toVectorMeasure A) :=
  QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten ρ.pos (M.positive A hA)

/-- The Born outcome law, obtained by applying the state trace functional to the POVM. -/
def born (M : MeasurablePOVM Ω I) (ρ : QIT.State I) : Measure Ω :=
  positiveScalarMeasure M (bornFunctional ρ) (bornFunctional_continuous ρ)
    (bornFunctional_nonneg M ρ)

theorem born_apply (M : MeasurablePOVM Ω I) (ρ : QIT.State I)
    {A : Set Ω} (hA : MeasurableSet A) :
    M.born ρ A = ENNReal.ofReal ((ρ.matrix * M.toVectorMeasure A).trace.re) :=
  positiveScalarMeasure_apply M _ _ _ hA

instance born_probability (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    IsProbabilityMeasure (M.born ρ) where
  measure_univ := by rw [born_apply M ρ MeasurableSet.univ, M.univ]; simp [ρ.trace_eq_one]

private def traceFunctional : Matrix I I ℂ →+ ℝ where
  toFun A := A.trace.re / Fintype.card I
  map_zero' := by simp
  map_add' A B := by simp [add_div]

omit [DecidableEq I] in
private theorem traceFunctional_continuous : Continuous (traceFunctional (I := I)) := by
  change Continuous (fun A : Matrix I I ℂ => A.trace.re / Fintype.card I)
  fun_prop

private theorem traceFunctional_nonneg (M : MeasurablePOVM Ω I)
    (A : Set Ω) (hA : MeasurableSet A) : 0 ≤ traceFunctional (M.toVectorMeasure A) :=
  div_nonneg (M.positive A hA).trace_nonneg.1 (Nat.cast_nonneg _)

/-- The normalized trace measure, the reference probability of SM IV.A. -/
def traceReference (M : MeasurablePOVM Ω I) : Measure Ω :=
  positiveScalarMeasure M traceFunctional traceFunctional_continuous
    (traceFunctional_nonneg M)

theorem traceReference_apply (M : MeasurablePOVM Ω I)
    {A : Set Ω} (hA : MeasurableSet A) :
    M.traceReference A =
      ENNReal.ofReal ((M.toVectorMeasure A).trace.re / Fintype.card I) :=
  positiveScalarMeasure_apply M _ _ _ hA

instance traceReference_probability [Nonempty I] (M : MeasurablePOVM Ω I) :
    IsProbabilityMeasure M.traceReference where
  measure_univ := by
    rw [traceReference_apply M MeasurableSet.univ, M.univ]
    simp [Fintype.card_ne_zero]

/-- A measurable set has zero reference mass precisely when its POVM effect vanishes. -/
theorem traceReference_eq_zero_iff [Nonempty I] (M : MeasurablePOVM Ω I)
    {A : Set Ω} (hA : MeasurableSet A) :
    M.traceReference A = 0 ↔ M.toVectorMeasure A = 0 := by
  rw [traceReference_apply M hA]
  constructor
  · intro hz
    have hn : 0 < (Fintype.card I : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have hle := (div_le_iff₀ hn).mp (ENNReal.ofReal_eq_zero.mp hz)
    have hre : (M.toVectorMeasure A).trace.re = 0 :=
      le_antisymm (by simpa using hle) (M.positive A hA).trace_nonneg.1
    apply (M.positive A hA).trace_eq_zero_iff.mp
    exact Complex.ext hre (M.positive A hA).trace_nonneg.2.symm
  · intro hz
    simp [hz]

/-- Every state's Born law is dominated by the same normalized trace probability. -/
theorem born_absolutelyContinuous [Nonempty I] (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    M.born ρ ≪ M.traceReference := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hz
  rw [born_apply M ρ hA, (M.traceReference_eq_zero_iff hA).mp hz]
  simp

private def scalarIdentity : ℝ →+ Matrix I I ℂ where
  toFun r := r • 1
  map_zero' := zero_smul _ _
  map_add' r s := add_smul r s _

omit [Fintype I] in
private theorem scalarIdentity_continuous : Continuous (scalarIdentity (I := I)) := by
  change Continuous (fun r : ℝ => r • (1 : Matrix I I ℂ))
  fun_prop

/-- A state-independent measurement with any prescribed classical probability law. -/
def ofProbability (μ : Measure Ω) [IsProbabilityMeasure μ] : MeasurablePOVM Ω I where
  toVectorMeasure := μ.toSignedMeasure.mapRange scalarIdentity scalarIdentity_continuous
  positive A hA := by
    simp only [VectorMeasure.mapRange_apply, Measure.toSignedMeasure_apply_measurable hA,
      scalarIdentity, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact Matrix.PosSemidef.one.smul measureReal_nonneg
  univ := by
    simp [VectorMeasure.mapRange_apply, scalarIdentity]

theorem ofProbability_apply (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : MeasurableSet A) :
    (ofProbability (I := I) μ).toVectorMeasure A = μ.real A • (1 : Matrix I I ℂ) := by
  simp only [ofProbability, VectorMeasure.mapRange_apply,
    Measure.toSignedMeasure_apply_measurable hA, scalarIdentity,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]

theorem born_ofProbability (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ : QIT.State I) :
    (ofProbability (I := I) μ).born ρ = μ := by
  ext A hA
  rw [born_apply _ ρ hA, ofProbability_apply μ hA]
  simp [Matrix.trace_smul, ρ.trace_eq_one, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top μ A)]

theorem traceReference_ofProbability [Nonempty I] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (ofProbability (I := I) μ).traceReference = μ := by
  ext A hA
  rw [traceReference_apply _ hA, ofProbability_apply μ hA]
  simp [Matrix.trace_smul, Fintype.card_ne_zero, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top μ A)]

end MeasurablePOVM
end LocalCertification.Quantum
