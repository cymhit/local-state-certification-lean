import LocalCertification.Quantum.MeasurablePOVMFrame
import CertificationGaussian.ProductFrameNet

/-! Actual arbitrary measurable POVMs belong to the fixed canonical frame family.
The witness uses the measurable orthonormal spectral basis of the trace density
and its eigenvalue-weighted refinement reference, including zero-weight outcomes.
-/

noncomputable section
open MeasureTheory Matrix CertificationGaussian
open scoped Matrix.Norms.L2Operator
namespace LocalCertification.Quantum.MeasurablePOVM
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Nonempty I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The genuine complex frame of the actual normalized refinement effects. -/
def refinementComplexFrame (M : MeasurablePOVM Ω I) : ComplexMatrixFrameSpace I :=
  integralComplexMatrixFrame M.refinementReference (fun p => M.refinementProjector p.1 p.2)

theorem refinementComplexFrame_mem_canonical (M : MeasurablePOVM Ω I) :
    M.refinementComplexFrame ∈ canonicalRankOneFrames (I := I) := by
  have hm : (∫ p, vectorRankOne (M.refinementUnitVector p.1 p.2)
      (M.refinementUnitVector p.1 p.2) ∂M.refinementReference) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ) := by
    simpa only [M.refinementProjector_eq_vectorRankOne, one_div,
      Complex.ofReal_inv, Complex.ofReal_natCast] using M.refinementProjector_mean
  have h := measurableRankOneFrame_mem_canonical M.refinementReference
    (fun p => M.refinementUnitVector p.1 p.2) M.refinementUnitVector_measurable
    (fun p => M.refinementUnitVector_norm p.1 p.2) hm
  have he : (fun p : Ω × I => vectorRankOne (M.refinementUnitVector p.1 p.2)
      (M.refinementUnitVector p.1 p.2)) = (fun p => M.refinementProjector p.1 p.2) := by
    funext p
    exact (M.refinementProjector_eq_vectorRankOne p.1 p.2).symm
  exact Eq.mp (congrArg (fun B => integralComplexMatrixFrame M.refinementReference B ∈
    canonicalRankOneFrames (I := I)) he) h

/-- A canonical frame carrying the actual POVM's frame, with its measure witness. -/
def refinementCanonicalFrame (M : MeasurablePOVM Ω I) : canonicalRankOneFrames (I := I) :=
  ⟨M.refinementComplexFrame, M.refinementComplexFrame_mem_canonical⟩

theorem refinementCanonicalFrame_coe (M : MeasurablePOVM Ω I) :
    (M.refinementCanonicalFrame).val = M.refinementComplexFrame := rfl

theorem refinementComplexFrame_norm_le (M : MeasurablePOVM Ω I) :
    ‖M.refinementComplexFrame‖ ≤ (Fintype.card I : ℝ)⁻¹ :=
  canonicalRankOneFrames_norm_le M.refinementCanonicalFrame

theorem refinementProjector_measurable_pair (M : MeasurablePOVM Ω I) :
    Measurable (fun p : Ω × I => M.refinementProjector p.1 p.2) :=
  measurable_from_prod_countable_left M.refinementProjector_measurable

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
theorem refinementProjector_hilbertSchmidt_norm (M : MeasurablePOVM Ω I) (p : Ω × I) :
    ‖matrixHilbertSchmidt (M.refinementProjector p.1 p.2)‖ = 1 := by
  rw [M.refinementProjector_eq_vectorRankOne]
  exact matrixHilbertSchmidt_unitProjector_norm _ (M.refinementUnitVector_norm p.1 p.2)

section Product
variable {S : Type*} [Fintype S] [DecidableEq S]
  {Ωs : S → Type*} [∀ s, MeasurableSpace (Ωs s)]

/-- The fixed family is chosen independently of every outcome space and POVM. -/
theorem productRefinementComplexFrame_mem_family
    (M : ∀ s, MeasurablePOVM (Ωs s) I) (J : Finset ℕ) (θ : ℕ → ℝ) :
    (signedProductMatrixFrame J θ (fun s => (M s).refinementComplexFrame)).restrictScalars ℝ ∈
      signedProductFrameFamily (S := S) (I := I) J θ :=
  ⟨fun s => (M s).refinementComplexFrame,
    fun s => subset_closure (M s).refinementComplexFrame_mem_canonical, rfl⟩

theorem productRefinementComplexFrame_eq_kernelFrame
    (M : ∀ s, MeasurablePOVM (Ωs s) I) (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) :
    integralComplexMatrixFrame (Measure.pi (fun s => (M s).refinementReference))
      (fun ω => cardinalityProjectorKernel
        (fun s => (M s).refinementProjector (ω s).1 (ω s).2) J θ) =
      signedProductMatrixFrame J θ (fun s => (M s).refinementComplexFrame) :=
  integralComplexMatrixFrame_signedProduct (fun s => (M s).refinementReference)
    (fun s p => (M s).refinementProjector p.1 p.2)
    (fun s => (M s).refinementProjector_measurable_pair)
    (fun s => (M s).refinementProjector_hilbertSchmidt_norm)
    (fun s p => (M s).refinementProjector_trace p.1 p.2) hd J θ

/-- The literal actual product-kernel integral is in the same parameter-independent family. -/
theorem productRefinementKernelFrame_mem_family
    (M : ∀ s, MeasurablePOVM (Ωs s) I) (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) :
    (integralComplexMatrixFrame (Measure.pi (fun s => (M s).refinementReference))
      (fun ω => cardinalityProjectorKernel
        (fun s => (M s).refinementProjector (ω s).1 (ω s).2) J θ)).restrictScalars ℝ ∈
          signedProductFrameFamily (S := S) (I := I) J θ := by
  rw [productRefinementComplexFrame_eq_kernelFrame M hd J θ]
  exact productRefinementComplexFrame_mem_family M J θ

end Product
end LocalCertification.Quantum.MeasurablePOVM
