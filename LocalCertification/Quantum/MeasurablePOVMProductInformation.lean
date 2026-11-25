import LocalCertification.Quantum.MeasurablePOVMProductRefinement
import LocalCertification.Quantum.MeasurablePOVMInformation

/-!
# Information of actual arbitrary-outcome product measurements

The original product Born laws coarse-grain the explicit local rank-one
refinement with the same reference pushforward. A positive operator background
in the denominator state bounds the original ordered KL by the actual refined
tensor-projector squared integral.
-/
set_option autoImplicit false
open MeasureTheory Matrix InformationTheory
open scoped ENNReal ComplexOrder MatrixOrder
noncomputable section
namespace LocalCertification.Quantum.MeasurablePOVM
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- The actual original reference L² difference contracts under forgetting
the finite local refinement indices. -/
theorem product_referenceL2_sq_le_localRefinement (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ σ : QIT.State (ι → α)) :
    (∫ s, ((product M).bornDensity ρ s - (product M).bornDensity σ s)^2
      ∂(product M).traceReference) ≤
        ∫ p, (productRefinedBornDensity M ρ p - productRefinedBornDensity M σ p)^2
          ∂productRefinementReference M := by
  have hmap : (productRefinementReference M).map productForget = (product M).traceReference :=
    (productRefinementReference_map M).trans (product_traceReference M).symm
  have hpush (τ : QIT.State (ι → α)) :
      ((productRefinementReference M).withDensity
        (fun p => ENNReal.ofReal (productRefinedBornDensity M τ p))).map productForget =
      (product M).traceReference.withDensity
        (fun s => ENNReal.ofReal ((product M).bornDensity τ s)) := by
    rw [← productRefined_born_eq_density M τ, productRefined_born_map M τ,
      (product M).born_eq_withDensity τ]
  exact Information.DensityCoarsening.integral_difference_sq_le
    (productRefinementReference M) (product M).traceReference productForget
    productForget_measurable hmap
    (productRefinedBornDensity M ρ) (productRefinedBornDensity M σ)
    ((product M).bornDensity ρ) ((product M).bornDensity σ)
    (productRefinedBornDensity_measurable M ρ) (productRefinedBornDensity_measurable M σ)
    ((product M).bornDensity_measurable ρ) ((product M).bornDensity_measurable σ)
    (Fintype.card (ι → α)) (Nat.cast_nonneg _)
    (fun p => ⟨productRefinedBornDensity_nonneg M ρ p, productRefinedBornDensity_le M ρ p⟩)
    (fun p => ⟨productRefinedBornDensity_nonneg M σ p, productRefinedBornDensity_le M σ p⟩)
    (fun s => ⟨(product M).bornDensity_nonneg ρ s, (product M).bornDensity_le ρ s⟩)
    (fun s => ⟨(product M).bornDensity_nonneg σ s, (product M).bornDensity_le σ s⟩)
    (hpush ρ) (hpush σ)

/-- Under the refined reference law the physical quadratic distance is the
integral of the explicit rank-one tensor readout. -/
theorem productRefined_reference_sq_eq (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ σ : QIT.State (ι → α)) :
    (∫ p, ((productRefined M).bornDensity ρ p - (productRefined M).bornDensity σ p)^2
      ∂(productRefined M).traceReference) =
    ∫ p, (productRefinedBornDensity M ρ p - productRefinedBornDensity M σ p)^2
      ∂productRefinementReference M := by
  rw [productRefined_traceReference]
  apply integral_congr_ae
  filter_upwards [productRefined_traceDensity_eq_tensor_ae M] with p hp
  simp only [bornDensity, productRefinedBornDensity, hp]

/-- Forgetting the local refinement indices contracts relative entropy for
the same ordered pair of physical states. -/
theorem product_klDiv_le_localRefinement (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ σ : QIT.State (ι → α)) :
    klDiv ((product M).born ρ) ((product M).born σ) ≤
      klDiv ((productRefined M).born ρ) ((productRefined M).born σ) := by
  rw [← productRefined_born_map M ρ, ← productRefined_born_map M σ]
  exact Information.DensityCoarsening.klDiv_coarsen_le _ _ productForget productForget_measurable

/-- Ordered original Born KL is controlled by the explicit refined reference
distance under a genuine positive maximally mixed operator background. -/
theorem product_born_klDiv_le_refined_sq (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ σ : QIT.State (ι → α)) (β : ℝ) (hβ : 0 < β)
    (hfloor : (σ.matrix - β • (QIT.State.maximallyMixed (ι → α)).matrix).PosSemidef) :
    klDiv ((product M).born ρ) ((product M).born σ) ≤
      ENNReal.ofReal (β⁻¹ * ∫ p,
        (productRefinedBornDensity M ρ p - productRefinedBornDensity M σ p)^2
          ∂productRefinementReference M) := by
  refine (product_klDiv_le_localRefinement M ρ σ).trans ?_
  simpa only [productRefined_reference_sq_eq] using
    (productRefined M).born_klDiv_le_reference_sq ρ σ β hβ hfloor

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinedBornDensity_sub (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ σ : QIT.State (ι → α)) (p : (i : ι) → Ω i × α) :
    productRefinedBornDensity M ρ p - productRefinedBornDensity M σ p =
      (Fintype.card (ι → α) : ℝ) *
        ((ρ.matrix - σ.matrix) * productRefinementProjector M p).trace.re := by
  rw [productRefinedBornDensity_eq, productRefinedBornDensity_eq,
    Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  ring

omit [MeasurableSingletonClass α] in
theorem product_refined_difference_sq_integral (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ σ : QIT.State (ι → α)) :
    (∫ p, (productRefinedBornDensity M ρ p - productRefinedBornDensity M σ p)^2
      ∂productRefinementReference M) =
        (Fintype.card (ι → α) : ℝ)^2 *
          ∫ p, (((ρ.matrix - σ.matrix) * productRefinementProjector M p).trace.re)^2
            ∂productRefinementReference M := by
  calc
    _ = ∫ p, (Fintype.card (ι → α) : ℝ)^2 *
        (((ρ.matrix - σ.matrix) * productRefinementProjector M p).trace.re)^2
          ∂productRefinementReference M := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by
        dsimp only
        rw [productRefinedBornDensity_sub]
        ring)
    _ = _ := integral_const_mul _ _

/-- The complete physical product Born information bound, expressed directly
as the tensor rank-one integral used by the frame/variance argument. -/
theorem product_born_klDiv_le_tensor_sq (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ σ : QIT.State (ι → α)) (β : ℝ) (hβ : 0 < β)
    (hfloor : (σ.matrix - β • (QIT.State.maximallyMixed (ι → α)).matrix).PosSemidef) :
    klDiv ((product M).born ρ) ((product M).born σ) ≤
      ENNReal.ofReal (β⁻¹ * (Fintype.card (ι → α) : ℝ)^2 *
        ∫ p, (((ρ.matrix - σ.matrix) * productRefinementProjector M p).trace.re)^2
          ∂productRefinementReference M) := by
  simpa only [product_refined_difference_sq_integral, mul_assoc] using
    product_born_klDiv_le_refined_sq M ρ σ β hβ hfloor

end LocalCertification.Quantum.MeasurablePOVM
