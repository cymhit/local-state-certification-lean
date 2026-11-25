import LocalCertification.Quantum.MeasurablePOVM
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Probability.Kernel.Basic

/-!
# Eventwise measurable families of original POVMs

An executable family requires measurability of every original event effect.
The resulting Born kernel uses the original measurement and outcome labels.
No joint measurable choice of RN densities or rank-one refinements is required.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
noncomputable section
namespace LocalCertification.Quantum

/-- A family of actual POVMs whose event effects depend measurably on the setting/history. -/
structure POVMKernel (H Ω I : Type*) [MeasurableSpace H] [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] where
  measurement : H → MeasurablePOVM Ω I
  measurable_effect : ∀ A, MeasurableSet A → Measurable (fun h => (measurement h).toVectorMeasure A)

namespace POVMKernel
variable {H Ω I : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I]

/-- The executable Born kernel for a fixed unknown state. -/
def bornKernel (K : POVMKernel H Ω I) (ρ : QIT.State I) : Kernel H Ω where
  toFun h := (K.measurement h).born ρ
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
    have hc : Continuous (fun B : Matrix I I ℂ => (ρ.matrix * B).trace.re) := by fun_prop
    have hm := ENNReal.measurable_ofReal.comp (hc.measurable.comp (K.measurable_effect A hA))
    simpa only [MeasurablePOVM.born_apply _ ρ hA, Function.comp_def] using hm

theorem bornKernel_apply (K : POVMKernel H Ω I) (ρ : QIT.State I) (h : H) :
    K.bornKernel ρ h = (K.measurement h).born ρ := rfl

theorem bornKernel_apply_event (K : POVMKernel H Ω I) (ρ : QIT.State I) (h : H)
    {A : Set Ω} (hA : MeasurableSet A) :
    K.bornKernel ρ h A =
      ENNReal.ofReal ((ρ.matrix * (K.measurement h).toVectorMeasure A).trace.re) :=
  (K.measurement h).born_apply ρ hA

instance bornKernel_markov (K : POVMKernel H Ω I) (ρ : QIT.State I) :
    IsMarkovKernel (K.bornKernel ρ) where
  isProbabilityMeasure h := (K.measurement h).born_probability ρ

/-- The original trace reference is itself an eventwise measurable kernel. -/
def traceKernel (K : POVMKernel H Ω I) : Kernel H Ω where
  toFun h := (K.measurement h).traceReference
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
    have hc : Continuous (fun B : Matrix I I ℂ => B.trace.re / Fintype.card I) := by fun_prop
    have hm := ENNReal.measurable_ofReal.comp (hc.measurable.comp (K.measurable_effect A hA))
    simpa only [MeasurablePOVM.traceReference_apply _ hA, Function.comp_def] using hm

theorem traceKernel_apply (K : POVMKernel H Ω I) (h : H) :
    K.traceKernel h = (K.measurement h).traceReference := rfl

instance traceKernel_markov [Nonempty I] (K : POVMKernel H Ω I) :
    IsMarkovKernel K.traceKernel where
  isProbabilityMeasure h := (K.measurement h).traceReference_probability

theorem bornKernel_absolutelyContinuous [Nonempty I] (K : POVMKernel H Ω I)
    (ρ : QIT.State I) (h : H) : K.bornKernel ρ h ≪ K.traceKernel h :=
  (K.measurement h).born_absolutelyContinuous ρ

/-- Reindex the setting by any measurable function of the full recorded history. -/
def reindex {G : Type*} [MeasurableSpace G] (K : POVMKernel H Ω I)
    (f : G → H) (hf : Measurable f) : POVMKernel G Ω I where
  measurement g := K.measurement (f g)
  measurable_effect A hA := (K.measurable_effect A hA).comp hf

theorem bornKernel_reindex_apply {G : Type*} [MeasurableSpace G] (K : POVMKernel H Ω I)
    (f : G → H) (hf : Measurable f) (ρ : QIT.State I) (g : G) :
    (K.reindex f hf).bornKernel ρ g = K.bornKernel ρ (f g) := rfl

/-- A fixed arbitrary-outcome POVM is an executable setting-independent family. -/
def constant (M : MeasurablePOVM Ω I) : POVMKernel H Ω I where
  measurement _ := M
  measurable_effect _ _ := measurable_const

theorem bornKernel_constant_apply (M : MeasurablePOVM Ω I) (ρ : QIT.State I) (h : H) :
    (constant M).bornKernel ρ h = M.born ρ := rfl

end POVMKernel
end LocalCertification.Quantum
