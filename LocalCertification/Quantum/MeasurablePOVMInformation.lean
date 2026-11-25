import LocalCertification.Quantum.MeasurablePOVMCoarsening
import LocalCertification.Information.DensityInformation

/-! Ordered relative entropy for the actual Born laws of an arbitrary measurable
POVM.  A positive maximally mixed operator background gives a pointwise reference
density floor; the reference squared-distance then controls KL. -/

set_option autoImplicit false
open MeasureTheory Matrix InformationTheory
open scoped ENNReal ComplexOrder MatrixOrder
noncomputable section

namespace LocalCertification.Quantum.MeasurablePOVM

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Nonempty I]

/-- An operator background yields a floor for every outcome reference density. -/
theorem bornDensity_ge_of_floor (M : MeasurablePOVM Ω I) (σ : QIT.State I) (β : ℝ)
    (hfloor : (σ.matrix - β • (QIT.State.maximallyMixed I).matrix).PosSemidef) (s : Ω) :
    β ≤ M.bornDensity σ s := by
  have ht := QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten hfloor (M.traceDensity_pos s)
  have hm := M.bornDensity_maximallyMixed s
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul] at ht
  change 0 ≤ M.bornDensity σ s - β * M.bornDensity (QIT.State.maximallyMixed I) s at ht
  rw [hm, mul_one] at ht
  exact sub_nonneg.mp ht

/-- The actual ordered Born KL is bounded by reference L2 distance divided by
the denominator state's positive maximally mixed background. -/
theorem born_klDiv_le_reference_sq (M : MeasurablePOVM Ω I) (ρ σ : QIT.State I)
    (β : ℝ) (hβ : 0 < β)
    (hfloor : (σ.matrix - β • (QIT.State.maximallyMixed I).matrix).PosSemidef) :
    klDiv (M.born ρ) (M.born σ) ≤
      ENNReal.ofReal (β⁻¹ * ∫ s, (M.bornDensity ρ s - M.bornDensity σ s)^2 ∂M.traceReference) := by
  exact Information.DensityInformation.klDiv_le_reference_sq
    M.traceReference (M.born ρ) (M.born σ) (M.bornDensity ρ) (M.bornDensity σ)
    (M.bornDensity_measurable ρ) (M.bornDensity_measurable σ) (Fintype.card I) β hβ
    (fun s => ⟨M.bornDensity_nonneg ρ s, M.bornDensity_le ρ s⟩)
    (fun s => ⟨M.bornDensity_ge_of_floor σ β hfloor s, M.bornDensity_le σ s⟩)
    (M.born_eq_withDensity ρ) (M.born_eq_withDensity σ)

end LocalCertification.Quantum.MeasurablePOVM
