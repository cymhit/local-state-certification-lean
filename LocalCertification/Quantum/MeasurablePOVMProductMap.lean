import LocalCertification.Quantum.MeasurablePOVMProductKernel
import LocalCertification.Quantum.MeasurablePOVMMap

/-! Actual product POVMs commute with coordinatewise measurable outcome maps.
This includes heterogeneous-universe relabeling and noninjective coarsening.
The equality is proved for matrix measures on all events, hence for every
global state, including entangled states. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
noncomputable section

namespace LocalCertification.Quantum.MeasurablePOVM

def productOutcomeMap {ι : Type*} {Ω Ξ : ι → Type*}
    (f : ∀ i, Ω i → Ξ i) (s : (i : ι) → Ω i) : (i : ι) → Ξ i := fun i => f i (s i)

theorem productOutcomeMap_measurable {ι : Type*} {Ω Ξ : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Ξ i)]
    (f : ∀ i, Ω i → Ξ i) (hf : ∀ i, Measurable (f i)) : Measurable (productOutcomeMap f) :=
  Measurable.of_eval fun i => (hf i).comp (measurable_pi_apply i)

private theorem productOutcomeMap_preimage_pi {ι : Type*} {Ω Ξ : ι → Type*}
    (f : ∀ i, Ω i → Ξ i) (A : ∀ i, Set (Ξ i)) :
    productOutcomeMap f ⁻¹' (Set.univ.pi A) = Set.univ.pi (fun i => f i ⁻¹' A i) := by
  ext s
  simp only [productOutcomeMap, Set.mem_preimage, Set.mem_univ_pi]

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Nonempty α]
  {Ω Ξ : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Ξ i)]

/-- Coordinatewise measurable coarsening commutes with the actual product measurement. -/
theorem product_map (M : ∀ i, MeasurablePOVM (Ω i) α)
    (f : ∀ i, Ω i → Ξ i) (hf : ∀ i, Measurable (f i)) :
    product (fun i => (M i).map (f i) (hf i)) =
      (product M).map (productOutcomeMap f) (productOutcomeMap_measurable f hf) := by
  apply ext_vectorMeasure
  let C : Set (Set ((i : ι) → Ξ i)) :=
    Set.pi Set.univ '' Set.pi Set.univ (fun i => {s : Set (Ξ i) | MeasurableSet s})
  have hgen : (inferInstance : MeasurableSpace ((i : ι) → Ξ i)) =
      MeasurableSpace.generateFrom C := generateFrom_pi.symm
  refine VectorMeasure.ext_of_generateFrom C ?_ hgen isPiSystem_pi ?_
  · intro A hA
    rcases hA with ⟨B, hB, rfl⟩
    have hBm : ∀ i, MeasurableSet (B i) := fun i => hB i (Set.mem_univ i)
    rw [product_apply_pi _ B hBm, map_apply _ _ _ (MeasurableSet.univ_pi hBm),
      productOutcomeMap_preimage_pi, product_apply_pi _ _ (fun i => hf i (hBm i))]
    congr 1
    funext i
    exact (M i).map_apply (f i) (hf i) (hBm i)
  · rw [(product (fun i => (M i).map (f i) (hf i))).univ,
      ((product M).map (productOutcomeMap f) (productOutcomeMap_measurable f hf)).univ]

/-- The relabeling case needed for independent-universe local outcome transport. -/
theorem product_map_equiv (M : ∀ i, MeasurablePOVM (Ω i) α) (e : ∀ i, Ω i ≃ᵐ Ξ i) :
    product (fun i => (M i).map (e i) (e i).measurable) =
      (product M).map (fun s i => e i (s i))
        (productOutcomeMap_measurable (fun i => e i) (fun i => (e i).measurable)) :=
  product_map M (fun i => e i) (fun i => (e i).measurable)

theorem product_born_map (M : ∀ i, MeasurablePOVM (Ω i) α)
    (f : ∀ i, Ω i → Ξ i) (hf : ∀ i, Measurable (f i)) (ρ : QIT.State (ι → α)) :
    (product (fun i => (M i).map (f i) (hf i))).born ρ =
      ((product M).born ρ).map (productOutcomeMap f) :=
  (congrArg (fun N => N.born ρ) (product_map M f hf)).trans
    ((product M).born_map _ (productOutcomeMap_measurable f hf) ρ)

theorem product_traceReference_map (M : ∀ i, MeasurablePOVM (Ω i) α)
    (f : ∀ i, Ω i → Ξ i) (hf : ∀ i, Measurable (f i)) :
    (product (fun i => (M i).map (f i) (hf i))).traceReference =
      (product M).traceReference.map (productOutcomeMap f) :=
  (congrArg MeasurablePOVM.traceReference (product_map M f hf)).trans
    ((product M).traceReference_map _ (productOutcomeMap_measurable f hf))

end LocalCertification.Quantum.MeasurablePOVM
namespace LocalCertification.Quantum.POVMKernel

variable {H ι α : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α] [Nonempty α]
  {Ω Ξ : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Ξ i)]

theorem product_map (K : ∀ i, POVMKernel H (Ω i) α)
    (f : ∀ i, Ω i → Ξ i) (hf : ∀ i, Measurable (f i)) :
    product (fun i => (K i).map (f i) (hf i)) =
      (product K).map (MeasurablePOVM.productOutcomeMap f)
        (MeasurablePOVM.productOutcomeMap_measurable f hf) :=
  ext_measurement fun h => MeasurablePOVM.product_map (fun i => (K i).measurement h) f hf

theorem product_map_equiv (K : ∀ i, POVMKernel H (Ω i) α) (e : ∀ i, Ω i ≃ᵐ Ξ i) :
    product (fun i => (K i).map (e i) (e i).measurable) =
      (product K).map (fun s i => e i (s i))
        (MeasurablePOVM.productOutcomeMap_measurable (fun i => e i) (fun i => (e i).measurable)) :=
  product_map K (fun i => e i) (fun i => (e i).measurable)

theorem product_bornKernel_map (K : ∀ i, POVMKernel H (Ω i) α)
    (f : ∀ i, Ω i → Ξ i) (hf : ∀ i, Measurable (f i)) (ρ : QIT.State (ι → α)) :
    (product (fun i => (K i).map (f i) (hf i))).bornKernel ρ =
      ((product K).bornKernel ρ).map (MeasurablePOVM.productOutcomeMap f) :=
  (congrArg (fun L => L.bornKernel ρ) (product_map K f hf)).trans
    ((product K).bornKernel_map _ (MeasurablePOVM.productOutcomeMap_measurable f hf) ρ)

theorem product_traceKernel_map (K : ∀ i, POVMKernel H (Ω i) α)
    (f : ∀ i, Ω i → Ξ i) (hf : ∀ i, Measurable (f i)) :
    (product (fun i => (K i).map (f i) (hf i))).traceKernel =
      (product K).traceKernel.map (MeasurablePOVM.productOutcomeMap f) :=
  (congrArg POVMKernel.traceKernel (product_map K f hf)).trans
    ((product K).traceKernel_map _ (MeasurablePOVM.productOutcomeMap_measurable f hf))

end LocalCertification.Quantum.POVMKernel
