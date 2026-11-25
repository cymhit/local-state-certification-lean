import LocalCertification.Quantum.MeasurablePOVMInformation
import LocalCertification.Information.ReferenceL2
import LocalCertification.Quantum.StateMixture

/-! Literal mixtures of density matrices and their common-reference Born bounds.
The parameter `t` is the weight of the second state.  The trace-reference measure
depends only on the POVM, so both state pairs are compared in the same `L²` space. -/

set_option autoImplicit false
open MeasureTheory Matrix InformationTheory
open scoped ENNReal ComplexOrder
noncomputable section

namespace LocalCertification.Quantum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual convex density matrix `(1-t) ρ + t σ`. -/
def binaryMixture (ρ σ : QIT.State I) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : QIT.State I where
  matrix := (1-t) • ρ.matrix + t • σ.matrix
  pos := (ρ.pos.smul (sub_nonneg.mpr ht1)).add (σ.pos.smul ht0)
  trace_eq_one := by
    simp only [Matrix.trace_add, Matrix.trace_smul, ρ.trace_eq_one, σ.trace_eq_one]
    rw [← add_smul]
    simp

theorem binaryMixture_fidelity (ψ : QIT.PureVector I) (ρ σ : QIT.State I)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pureTargetFidelity ψ (binaryMixture ρ σ t ht0 ht1) =
      (1-t) * pureTargetFidelity ψ ρ + t * pureTargetFidelity ψ σ := by
  simp only [pureTargetFidelity, binaryMixture, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]

/-- The first component retains its positive operator background with weight `1-t`. -/
theorem binaryMixture_floor (ρ σ ω : QIT.State I) (t β : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hfloor : (ρ.matrix - β • ω.matrix).PosSemidef) :
    ((binaryMixture ρ σ t ht0 ht1).matrix - ((1-t)*β) • ω.matrix).PosSemidef := by
  have h := (hfloor.smul (sub_nonneg.mpr ht1)).add (σ.pos.smul ht0)
  convert h using 1
  simp only [binaryMixture, smul_sub, smul_smul]
  abel

namespace MeasurablePOVM

variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty I]

theorem bornDensity_binaryMixture (M : MeasurablePOVM Ω I) (ρ σ : QIT.State I)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : Ω) :
    M.bornDensity (binaryMixture ρ σ t ht0 ht1) s =
      (1-t) * M.bornDensity ρ s + t * M.bornDensity σ s := by
  simp only [bornDensity, binaryMixture, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]

theorem bornDensity_memLp (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    MemLp (M.bornDensity ρ) 2 M.traceReference := by
  apply MemLp.of_bound (M.bornDensity_measurable ρ).aestronglyMeasurable (Fintype.card I)
  exact ae_of_all _ fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (M.bornDensity_nonneg ρ s)]
    exact M.bornDensity_le ρ s

/-- Literal mixed-state differences use one and the same reference density. -/
theorem bornDensity_binaryMixture_sub (M : MeasurablePOVM Ω I)
    (ρ₀ ρ₁ σ₀ σ₁ : QIT.State I) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (s : Ω) :
    M.bornDensity (binaryMixture ρ₀ ρ₁ t ht0 ht1) s -
      M.bornDensity (binaryMixture σ₀ σ₁ t ht0 ht1) s =
    (1-t) * (M.bornDensity ρ₀ s - M.bornDensity σ₀ s) +
      t * (M.bornDensity ρ₁ s - M.bornDensity σ₁ s) := by
  rw [M.bornDensity_binaryMixture, M.bornDensity_binaryMixture]
  ring

theorem referenceL2_binaryMixture_le (M : MeasurablePOVM Ω I)
    (ρ₀ ρ₁ σ₀ σ₁ : QIT.State I) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sqrt (∫ s, (M.bornDensity (binaryMixture ρ₀ ρ₁ t ht0 ht1) s -
      M.bornDensity (binaryMixture σ₀ σ₁ t ht0 ht1) s)^2 ∂M.traceReference) ≤
      (1-t) * Real.sqrt (∫ s, (M.bornDensity ρ₀ s - M.bornDensity σ₀ s)^2 ∂M.traceReference) +
      t * Real.sqrt (∫ s, (M.bornDensity ρ₁ s - M.bornDensity σ₁ s)^2 ∂M.traceReference) := by
  simp_rw [M.bornDensity_binaryMixture_sub]
  simpa only [abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0, Pi.sub_apply] using
    Information.ReferenceL2.sqrt_integral_square_combination_le M.traceReference
      (M.bornDensity ρ₀ - M.bornDensity σ₀) (M.bornDensity ρ₁ - M.bornDensity σ₁)
      ((M.bornDensity_memLp ρ₀).sub (M.bornDensity_memLp σ₀))
      ((M.bornDensity_memLp ρ₁).sub (M.bornDensity_memLp σ₁)) (1-t) t

theorem referenceL2_sq_binaryMixture_le (M : MeasurablePOVM Ω I)
    (ρ₀ ρ₁ σ₀ σ₁ : QIT.State I) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ s, (M.bornDensity (binaryMixture ρ₀ ρ₁ t ht0 ht1) s -
      M.bornDensity (binaryMixture σ₀ σ₁ t ht0 ht1) s)^2 ∂M.traceReference) ≤
      2*(1-t)^2*(∫ s, (M.bornDensity ρ₀ s - M.bornDensity σ₀ s)^2 ∂M.traceReference) +
      2*t^2*(∫ s, (M.bornDensity ρ₁ s - M.bornDensity σ₁ s)^2 ∂M.traceReference) := by
  simp_rw [M.bornDensity_binaryMixture_sub]
  exact Information.ReferenceL2.integral_square_combination_le M.traceReference
    (M.bornDensity ρ₀ - M.bornDensity σ₀) (M.bornDensity ρ₁ - M.bornDensity σ₁)
    ((M.bornDensity_memLp ρ₀).sub (M.bornDensity_memLp σ₀))
    ((M.bornDensity_memLp ρ₁).sub (M.bornDensity_memLp σ₁)) (1-t) t

/-- Ordered Born information for genuine mixed hard pairs. -/
theorem born_klDiv_binaryMixture_le (M : MeasurablePOVM Ω I)
    (ρ₀ ρ₁ σ₀ σ₁ : QIT.State I) (t β : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hβ : 0 < β)
    (hfloor : (σ₀.matrix - β • (QIT.State.maximallyMixed I).matrix).PosSemidef) :
    klDiv (M.born (binaryMixture ρ₀ ρ₁ t ht0 ht1.le))
      (M.born (binaryMixture σ₀ σ₁ t ht0 ht1.le)) ≤
      ENNReal.ofReal (((1-t)*β)⁻¹ *
        (2*(1-t)^2*(∫ s, (M.bornDensity ρ₀ s - M.bornDensity σ₀ s)^2 ∂M.traceReference) +
          2*t^2*(∫ s, (M.bornDensity ρ₁ s - M.bornDensity σ₁ s)^2 ∂M.traceReference))) := by
  have hpos := mul_pos (sub_pos.mpr ht1) hβ
  refine (M.born_klDiv_le_reference_sq _ _ _ hpos
    (binaryMixture_floor σ₀ σ₁ _ t β ht0 ht1.le hfloor)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (M.referenceL2_sq_binaryMixture_le ρ₀ ρ₁ σ₀ σ₁ t ht0 ht1.le) (inv_nonneg.mpr hpos.le)

end MeasurablePOVM
end LocalCertification.Quantum
