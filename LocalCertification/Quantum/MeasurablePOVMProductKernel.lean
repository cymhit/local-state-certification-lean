import LocalCertification.Quantum.MeasurablePOVMKernel
import LocalCertification.Quantum.MeasurablePOVMProduct

/-!
# Executable products of arbitrary local measurable POVM families

Measurability on rectangles follows from finite products of local matrix entries.
A generating π-system argument extends it to every measurable event by complement
and countable additivity. No jointly measurable RN densities are selected.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
noncomputable section
namespace LocalCertification.Quantum.POVMKernel
variable {H ι α : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α] [Nonempty α]
  {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- Eventwise measurability of the actual product follows from that of each local POVM. -/
theorem product_effect_measurable (K : ∀ i, POVMKernel H (Ω i) α)
    {A : Set ((i : ι) → Ω i)} (hA : MeasurableSet A) :
    Measurable (fun h =>
      (MeasurablePOVM.product (fun i => (K i).measurement h)).toVectorMeasure A) := by
  let C : Set (Set ((i : ι) → Ω i)) :=
    Set.pi Set.univ '' Set.pi Set.univ (fun i => {s : Set (Ω i) | MeasurableSet s})
  have hgen : (inferInstance : MeasurableSpace ((i : ι) → Ω i)) =
      MeasurableSpace.generateFrom C := generateFrom_pi.symm
  have hpi : IsPiSystem C := isPiSystem_pi
  induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
  | empty =>
    simp only [VectorMeasure.empty]
    exact measurable_const
  | basic A hA =>
    rcases hA with ⟨B, hB, rfl⟩
    have hBm : ∀ i, MeasurableSet (B i) := fun i => hB i (Set.mem_univ i)
    simp_rw [MeasurablePOVM.product_apply_pi _ B hBm]
    apply Measurable.of_eval_matrix
    intro x y
    exact Finset.measurable_prod _ (fun i _ =>
      ((K i).measurable_effect (B i) (hBm i)).eval_matrix (i := x i) (j := y i))
  | compl A hA ih =>
    apply Measurable.of_eval_matrix
    intro x y
    simp only [VectorMeasure.of_compl hA, MeasurablePOVM.univ, Matrix.sub_apply]
    exact measurable_const.sub (ih.eval_matrix (i := x) (j := y))
  | iUnion f hfd hfm ih =>
    apply Measurable.of_eval_matrix
    intro x y
    have he (h : H) :
        (MeasurablePOVM.product (fun i => (K i).measurement h)).toVectorMeasure (⋃ n, f n) x y =
          ∑' n, (MeasurablePOVM.product (fun i => (K i).measurement h)).toVectorMeasure (f n) x y := by
      have hs := (MeasurablePOVM.product (fun i => (K i).measurement h)).toVectorMeasure.hasSum_of_disjoint_iUnion hfm hfd
      exact (Pi.hasSum.mp (Pi.hasSum.mp hs x) y).tsum_eq.symm
    simp_rw [he]
    exact Measurable.tsum (fun n => (ih n).eval_matrix (i := x) (j := y))

/-- Execute all local measurements with the same history-dependent setting,
retaining their full original outcome tuple. -/
def product (K : ∀ i, POVMKernel H (Ω i) α) : POVMKernel H ((i : ι) → Ω i) (ι → α) where
  measurement h := MeasurablePOVM.product (fun i => (K i).measurement h)
  measurable_effect _ hA := product_effect_measurable K hA

theorem product_measurement (K : ∀ i, POVMKernel H (Ω i) α) (h : H) :
    (product K).measurement h = MeasurablePOVM.product (fun i => (K i).measurement h) := rfl

theorem product_bornKernel_apply (K : ∀ i, POVMKernel H (Ω i) α)
    (ρ : QIT.State (ι → α)) (h : H) :
    (product K).bornKernel ρ h =
      (MeasurablePOVM.product (fun i => (K i).measurement h)).born ρ := rfl

theorem product_traceKernel_apply (K : ∀ i, POVMKernel H (Ω i) α) (h : H) :
    (product K).traceKernel h = Measure.pi (fun i => (K i).traceKernel h) :=
  MeasurablePOVM.product_traceReference (fun i => (K i).measurement h)

/-- Rectangle probabilities remain the actual Born probabilities of tensor effects,
including for entangled global states. -/
theorem product_bornKernel_apply_pi (K : ∀ i, POVMKernel H (Ω i) α)
    (ρ : QIT.State (ι → α)) (h : H) (A : ∀ i, Set (Ω i))
    (hA : ∀ i, MeasurableSet (A i)) :
    (product K).bornKernel ρ h (Set.univ.pi A) = ENNReal.ofReal
      ((ρ.matrix * tensorMatrix (fun i => ((K i).measurement h).toVectorMeasure (A i))).trace.re) := by
  rw [product_bornKernel_apply, MeasurablePOVM.born_apply _ _ (MeasurableSet.univ_pi hA),
    MeasurablePOVM.product_apply_pi _ A hA]
end LocalCertification.Quantum.POVMKernel
