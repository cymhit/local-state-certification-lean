import LocalCertification.Protocol.FixedHorizon
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical Set
open scoped BigOperators ENNReal
noncomputable section
namespace LocalCertification.Protocol
universe u v w
variable {ι : Type u} [Fintype ι] {H : Type v} {O : Type w}
  [MeasurableSpace H] [MeasurableSpace O] [Fintype O] [MeasurableSingletonClass O]

/-- The actual conditional distribution of independent finite outcomes, keeping all pre-sampled labels. -/
def finiteProductKernel (κ : Kernel H O) [IsMarkovKernel κ] : Kernel (ι → H) (ι → O) where
  toFun z := Measure.pi (fun i => κ (z i))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s _
    have he (z : ι → H) : (Measure.pi (fun i => κ (z i))) s =
        ∑ x ∈ s.toFinite.toFinset, ∏ i, κ (z i) {x i} := by
      calc
        _ = (Measure.pi (fun i => κ (z i))) (s.toFinite.toFinset : Set (ι → O)) :=
          congrArg (Measure.pi (fun i => κ (z i))) s.toFinite.coe_toFinset.symm
        _ = ∑ x ∈ s.toFinite.toFinset, (Measure.pi (fun i => κ (z i))) {x} :=
          sum_measure_singleton.symm
        _ = _ := by simp only [Measure.pi_singleton]
    simp_rw [he]
    apply Finset.measurable_sum
    intro x _
    apply Finset.measurable_prod
    intro i _
    exact (κ.measurable_coe (measurableSet_singleton (x i))).comp (measurable_pi_apply i)

instance finiteProductKernel_markov (κ : Kernel H O) [IsMarkovKernel κ] :
    IsMarkovKernel (finiteProductKernel (ι := ι) κ) := ⟨fun z => by
    change IsProbabilityMeasure (Measure.pi (fun i : ι => κ (z i)))
    infer_instance⟩

@[simp] theorem finiteProductKernel_apply (κ : Kernel H O) [IsMarkovKernel κ] (z : ι → H) :
    finiteProductKernel κ z = Measure.pi (fun i => κ (z i)) := rfl

/-- The exact product-integral identity used for independent complete records. -/
theorem lintegral_independent_coordinates (μ : Measure H) [IsProbabilityMeasure μ]
    (g : ι → H → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    (∫⁻ z, ∏ i, g i (z i) ∂Measure.pi (fun _ : ι => μ)) = ∏ i, ∫⁻ h, g i h ∂μ := by
  have hind : iIndepFun (fun i (z : ι → H) => g i (z i)) (Measure.pi (fun _ : ι => μ)) :=
    iIndepFun_pi (fun i => (hg i).aemeasurable)
  calc
    _ = ∏ i, ∫⁻ z, g i (z i) ∂Measure.pi (fun _ : ι => μ) :=
      lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ (fun i (z : ι → H) => g i (z i)) hind
        (fun i => (hg i).comp (measurable_pi_apply i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (measurePreserving_eval (fun _ : ι => μ) i).lintegral_comp (hg i)

omit [Fintype ι] [Fintype O] [MeasurableSingletonClass O] in
/-- Zipping seed labels and physical outcomes is measurable in their original sigma algebras. -/
theorem completeRecords_measurable :
    Measurable (fun p : (ι → H) × (ι → O) => fun i => (p.1 i,p.2 i)) :=
  measurable_pi_iff.mpr (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_pi_apply i).comp measurable_snd))

/-- Independent labels followed by the actual conditional outcome product are exactly independent full records.
This keeps continuous label spaces and their original sigma algebras, without disintegration. -/
theorem independent_complete_records (μ : Measure H) [IsProbabilityMeasure μ]
    (κ : Kernel H O) [IsMarkovKernel κ] :
    ((Measure.pi (fun _ : ι => μ)) ⊗ₘ finiteProductKernel κ).map
      (fun p => fun i => (p.1 i,p.2 i)) = Measure.pi (fun _ : ι => μ ⊗ₘ κ) := by
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply completeRecords_measurable (MeasurableSet.univ_pi hs),
    Measure.compProd_apply ((MeasurableSet.univ_pi hs).preimage completeRecords_measurable)]
  have he (z : ι → H) :
      Prod.mk z ⁻¹' ((fun p : (ι → H) × (ι → O) => fun i => (p.1 i,p.2 i)) ⁻¹' Set.univ.pi s) =
      Set.univ.pi (fun i => Prod.mk (z i) ⁻¹' s i) := by ext x; simp
  simp_rw [finiteProductKernel_apply, he, Measure.pi_pi]
  rw [lintegral_independent_coordinates μ (fun i h => κ h (Prod.mk h ⁻¹' s i))
    (fun i => Kernel.measurable_kernel_prodMk_left (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (Measure.compProd_apply (hs i)).symm

end LocalCertification.Protocol
