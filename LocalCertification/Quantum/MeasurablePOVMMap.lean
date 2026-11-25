import LocalCertification.Quantum.MeasurablePOVMKernel
import Mathlib.Probability.Kernel.Composition.MapComap

/-! Arbitrary measurable outcome pushforwards of actual POVMs and executable
families.  Source and target outcome spaces may have different universes.
No standard Borel, injectivity, or finiteness assumption is used. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
noncomputable section

namespace LocalCertification.Quantum
namespace MeasurablePOVM

variable {Ω Ξ Υ I : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Υ]
  [Fintype I] [DecidableEq I]

theorem ext_vectorMeasure {M N : MeasurablePOVM Ω I}
    (h : M.toVectorMeasure = N.toVectorMeasure) : M = N := by
  cases M
  cases N
  cases h
  rfl

/-- Relabel or coarsen the outcomes by an arbitrary measurable map. -/
def map (M : MeasurablePOVM Ω I) (f : Ω → Ξ) (hf : Measurable f) : MeasurablePOVM Ξ I where
  toVectorMeasure := M.toVectorMeasure.map f
  positive A hA := by
    rw [VectorMeasure.map_apply _ hf hA]
    exact M.positive _ (hf hA)
  univ := by
    rw [VectorMeasure.map_apply _ hf MeasurableSet.univ, Set.preimage_univ, M.univ]

theorem map_toVectorMeasure (M : MeasurablePOVM Ω I) (f : Ω → Ξ) (hf : Measurable f) :
    (M.map f hf).toVectorMeasure = M.toVectorMeasure.map f := rfl

theorem map_apply (M : MeasurablePOVM Ω I) (f : Ω → Ξ) (hf : Measurable f)
    {A : Set Ξ} (hA : MeasurableSet A) :
    (M.map f hf).toVectorMeasure A = M.toVectorMeasure (f ⁻¹' A) :=
  VectorMeasure.map_apply _ hf hA

theorem born_map (M : MeasurablePOVM Ω I) (f : Ω → Ξ) (hf : Measurable f) (ρ : QIT.State I) :
    (M.map f hf).born ρ = (M.born ρ).map f := by
  ext A hA
  rw [born_apply _ ρ hA, Measure.map_apply hf hA, born_apply _ ρ (hf hA), map_apply _ f hf hA]

theorem traceReference_map (M : MeasurablePOVM Ω I) (f : Ω → Ξ) (hf : Measurable f) :
    (M.map f hf).traceReference = M.traceReference.map f := by
  ext A hA
  rw [traceReference_apply _ hA, Measure.map_apply hf hA, traceReference_apply _ (hf hA),
    map_apply _ f hf hA]

theorem map_id (M : MeasurablePOVM Ω I) : M.map id measurable_id = M := by
  apply ext_vectorMeasure
  exact VectorMeasure.map_id _

theorem map_comp (M : MeasurablePOVM Ω I) (f : Ω → Ξ) (hf : Measurable f)
    (g : Ξ → Υ) (hg : Measurable g) :
    (M.map f hf).map g hg = M.map (g ∘ f) (hg.comp hf) := by
  apply ext_vectorMeasure
  apply VectorMeasure.ext
  intro A hA
  rw [map_apply _ g hg hA, map_apply _ f hf (hg hA), map_apply _ (g ∘ f) (hg.comp hf) hA]
  rfl

theorem map_equiv_symm (M : MeasurablePOVM Ω I) (e : Ω ≃ᵐ Ξ) :
    (M.map e e.measurable).map e.symm e.symm.measurable = M := by
  apply ext_vectorMeasure
  apply VectorMeasure.ext
  intro A hA
  rw [map_apply _ e.symm e.symm.measurable hA, map_apply _ e e.measurable (e.symm.measurable hA)]
  congr 1
  ext x
  simp only [Set.mem_preimage, e.symm_apply_apply]

end MeasurablePOVM
namespace POVMKernel

variable {H Ω Ξ Υ I : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [MeasurableSpace Ξ] [MeasurableSpace Υ] [Fintype I] [DecidableEq I]

theorem ext_measurement {K L : POVMKernel H Ω I}
    (h : ∀ x, K.measurement x = L.measurement x) : K = L := by
  have he := funext h
  cases K
  cases L
  cases he
  rfl

/-- Measurable outcome transport preserves eventwise measurability in history. -/
def map (K : POVMKernel H Ω I) (f : Ω → Ξ) (hf : Measurable f) : POVMKernel H Ξ I where
  measurement h := (K.measurement h).map f hf
  measurable_effect A hA := by
    simpa only [MeasurablePOVM.map_apply _ f hf hA] using K.measurable_effect _ (hf hA)

theorem map_measurement (K : POVMKernel H Ω I) (f : Ω → Ξ) (hf : Measurable f) (h : H) :
    (K.map f hf).measurement h = (K.measurement h).map f hf := rfl

theorem bornKernel_map (K : POVMKernel H Ω I) (f : Ω → Ξ) (hf : Measurable f) (ρ : QIT.State I) :
    (K.map f hf).bornKernel ρ = (K.bornKernel ρ).map f := by
  ext1 h
  rw [Kernel.map_apply _ hf]
  exact (K.measurement h).born_map f hf ρ

theorem traceKernel_map (K : POVMKernel H Ω I) (f : Ω → Ξ) (hf : Measurable f) :
    (K.map f hf).traceKernel = K.traceKernel.map f := by
  ext1 h
  rw [Kernel.map_apply _ hf]
  exact (K.measurement h).traceReference_map f hf

theorem map_id (K : POVMKernel H Ω I) : K.map id measurable_id = K :=
  ext_measurement fun h => MeasurablePOVM.map_id (K.measurement h)

theorem map_comp (K : POVMKernel H Ω I) (f : Ω → Ξ) (hf : Measurable f)
    (g : Ξ → Υ) (hg : Measurable g) :
    (K.map f hf).map g hg = K.map (g ∘ f) (hg.comp hf) :=
  ext_measurement fun h => MeasurablePOVM.map_comp (K.measurement h) f hf g hg

theorem map_equiv_symm (K : POVMKernel H Ω I) (e : Ω ≃ᵐ Ξ) :
    (K.map e e.measurable).map e.symm e.symm.measurable = K :=
  ext_measurement fun h => MeasurablePOVM.map_equiv_symm (K.measurement h) e

end POVMKernel
end LocalCertification.Quantum
