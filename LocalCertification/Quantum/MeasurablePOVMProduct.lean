import LocalCertification.Quantum.MeasurablePOVMDensity
import LocalCertification.Quantum.TensorMatrix
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Products of arbitrary measurable local POVMs

The outcome spaces are arbitrary measurable spaces. The matrix measure is constructed
from the product trace reference and the tensor product of the proved RN densities.
Its value on every measurable rectangle is the tensor product of the original effects.
-/

set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.Elementwise
noncomputable section
namespace LocalCertification.Quantum

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Positivity of the function-indexed tensor product, including zero factors. -/
theorem tensorMatrix_posSemidef (A : ι → Matrix α α ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (tensorMatrix A).PosSemidef := by
  let B := fun i => QIT.psdSqrt (A i)
  have he : tensorMatrix A = tensorMatrix B * (tensorMatrix B).conjTranspose := by
    rw [← tensorMatrix_adjoint, ← tensorMatrix_mul]
    congr 1
    funext i
    exact ((congrArg (fun C => B i * C) (QIT.psdSqrt_isHermitian (A i)).eq).trans
      (QIT.psdSqrt_mul_self_of_posSemidef (hA i))).symm
  exact he ▸ Matrix.posSemidef_self_mul_conjTranspose _

namespace MeasurablePOVM
section IntegralHelpers
variable {I : Type*} [Fintype I]
local instance tensorIntegralContinuousENorm : ContinuousENorm (Matrix I I ℂ) :=
  SeminormedAddGroup.toContinuousENorm

private def entryMap (i j : I) : Matrix I I ℂ →L[ℝ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

private def adjointMap : Matrix I I ℂ →L[ℝ] Matrix I I ℂ where
  toFun A := A.conjTranspose
  map_add' A B := Matrix.conjTranspose_add A B
  map_smul' _ _ := by simp
  cont := by fun_prop

private def quadraticMap (v : I → ℂ) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (star v ⬝ᵥ (A *ᵥ v)).re
  map_add' _ _ := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' _ _ := by simp [Matrix.smul_mulVec, dotProduct_smul]
  cont := by unfold Matrix.mulVec dotProduct; fun_prop

private theorem integral_posSemidef {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {f : X → Matrix I I ℂ} (hf : Integrable f ν) (hp : ∀ x, (f x).PosSemidef) :
    (∫ x, f x ∂ν).PosSemidef := by
  have hH : (∫ x, f x ∂ν).IsHermitian := by
    exact (adjointMap.integral_comp_comm hf).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall (fun x => (hp x).isHermitian.eq)))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  constructor
  · have h : 0 ≤ ∫ x, quadraticMap v (f x) ∂ν :=
      integral_nonneg (fun x => (hp x).re_dotProduct_nonneg v)
    change 0 ≤ quadraticMap v (∫ x, f x ∂ν)
    exact ((quadraticMap v).integral_comp_comm hf) ▸ h
  · exact (hH.im_star_dotProduct_mulVec_self v).symm

private def normalizedTraceMap : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := A.trace.re / Fintype.card I
  map_add' _ _ := by simp [add_div]
  map_smul' _ _ := by simp [mul_div_assoc]
  cont := by fun_prop

private def stateMap [DecidableEq I] (ρ : QIT.State I) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (ρ.matrix * A).trace.re
  map_add' _ _ := by simp [Matrix.mul_add]
  map_smul' _ _ := by simp
  cont := by fun_prop
end IntegralHelpers

variable [Nonempty α] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
local instance localDensityContinuousENorm : ContinuousENorm (Matrix α α ℂ) :=
  SeminormedAddGroup.toContinuousENorm
local instance productDensityContinuousENorm : ContinuousENorm (Matrix (ι → α) (ι → α) ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The product of the actual local trace reference probabilities. -/
def productReference (M : ∀ i, MeasurablePOVM (Ω i) α) : Measure ((i : ι) → Ω i) :=
  Measure.pi (fun i => (M i).traceReference)

instance productReference_probability (M : ∀ i, MeasurablePOVM (Ω i) α) :
    IsProbabilityMeasure (productReference M) := by unfold productReference; infer_instance

/-- The tensor product of the actual local matrix RN densities. -/
def productDensity (M : ∀ i, MeasurablePOVM (Ω i) α) (s : (i : ι) → Ω i) :
    Matrix (ι → α) (ι → α) ℂ := tensorMatrix (fun i => (M i).traceDensity (s i))

omit [DecidableEq ι] in
theorem productDensity_measurable (M : ∀ i, MeasurablePOVM (Ω i) α) :
    Measurable (productDensity M) := by
  apply Measurable.of_eval_matrix
  intro x y
  exact Finset.measurable_prod _ (fun i _ =>
    ((M i).traceDensity_measurable.eval_matrix (i := x i) (j := y i)).comp
      (measurable_pi_apply i))

theorem productDensity_integrable (M : ∀ i, MeasurablePOVM (Ω i) α) :
    Integrable (productDensity M) (productReference M) := by
  apply Integrable.of_eval
  intro x
  apply Integrable.of_eval
  intro y
  exact Integrable.fintype_prod_dep (fun i =>
    (entryMap (x i) (y i)).integrable_comp (M i).traceDensity_integrable)

theorem productDensity_pos (M : ∀ i, MeasurablePOVM (Ω i) α) (s : (i : ι) → Ω i) :
    (productDensity M s).PosSemidef :=
  tensorMatrix_posSemidef _ (fun i => (M i).traceDensity_pos (s i))

theorem productDensity_trace (M : ∀ i, MeasurablePOVM (Ω i) α) (s : (i : ι) → Ω i) :
    (productDensity M s).trace = (Fintype.card (ι → α) : ℂ) := by
  simp only [productDensity, tensorMatrix_trace, traceDensity_trace, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Nat.cast_pow]

theorem productDensity_setIntegral_pi (M : ∀ i, MeasurablePOVM (Ω i) α)
    (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i)) :
    ∫ s in Set.univ.pi A, productDensity M s ∂productReference M =
      tensorMatrix (fun i => (M i).toVectorMeasure (A i)) := by
  ext x y
  change entryMap x y (∫ s in Set.univ.pi A, productDensity M s ∂productReference M) = _
  refine ((entryMap x y).integral_comp_comm
    (productDensity_integrable M).integrableOn).symm.trans ?_
  change (∫ s, ∏ i, (M i).traceDensity (s i) (x i) (y i)
    ∂(Measure.pi (fun i => (M i).traceReference)).restrict (Set.univ.pi A)) = _
  rw [Measure.restrict_pi_pi]
  refine (integral_fintype_prod_eq_prod
    (μ := fun i => (M i).traceReference.restrict (A i))
    (fun i s => (M i).traceDensity s (x i) (y i))).trans ?_
  apply Finset.prod_congr rfl
  intro i _
  exact ((entryMap (x i) (y i)).integral_comp_comm
    (M i).traceDensity_integrable.integrableOn).trans
      (congrArg (fun B => entryMap (x i) (y i) B) ((M i).traceDensity_setIntegral (hA i)))

private theorem integral_productDensity (M : ∀ i, MeasurablePOVM (Ω i) α) :
    ∫ s, productDensity M s ∂productReference M = 1 := by
  have h := productDensity_setIntegral_pi M (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  simpa only [Set.pi_univ, Measure.restrict_univ, MeasurablePOVM.univ, tensorMatrix_one] using h

/-- The genuine product POVM, with all original local outcome labels retained. -/
def product (M : ∀ i, MeasurablePOVM (Ω i) α) : MeasurablePOVM ((i : ι) → Ω i) (ι → α) where
  toVectorMeasure := (productReference M).withDensityᵥ (productDensity M)
  positive A hA := by
    have h : (∫ s in A, productDensity M s ∂productReference M).PosSemidef :=
      integral_posSemidef _ (productDensity_integrable M).integrableOn (productDensity_pos M)
    exact (withDensityᵥ_apply (productDensity_integrable M) hA).symm ▸ h
  univ := (withDensityᵥ_apply (productDensity_integrable M) MeasurableSet.univ).trans
    (by simpa only [Measure.restrict_univ] using integral_productDensity M)

theorem product_apply (M : ∀ i, MeasurablePOVM (Ω i) α) {A : Set ((i : ι) → Ω i)}
    (hA : MeasurableSet A) :
    (product M).toVectorMeasure A = ∫ s in A, productDensity M s ∂productReference M :=
  withDensityᵥ_apply (productDensity_integrable M) hA

/-- The product measure has exactly the tensor effects on every measurable rectangle. -/
theorem product_apply_pi (M : ∀ i, MeasurablePOVM (Ω i) α)
    (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i)) :
    (product M).toVectorMeasure (Set.univ.pi A) =
      tensorMatrix (fun i => (M i).toVectorMeasure (A i)) :=
  (product_apply M (MeasurableSet.univ_pi hA)).trans (productDensity_setIntegral_pi M A hA)

/-- The product reference is the normalized trace of the actual product POVM. -/
theorem product_traceReference (M : ∀ i, MeasurablePOVM (Ω i) α) :
    (product M).traceReference = Measure.pi (fun i => (M i).traceReference) := by
  apply Measure.ext
  intro A hA
  rw [(product M).traceReference_apply hA]
  have h : normalizedTraceMap ((product M).toVectorMeasure A) = (productReference M).real A := by
    refine (congrArg (fun B => normalizedTraceMap B) (product_apply M hA)).trans ?_
    refine (normalizedTraceMap.integral_comp_comm
      (productDensity_integrable M).integrableOn).symm.trans ?_
    refine (integral_congr_ae (g := fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall (fun s => ?_))).trans ?_
    · change (productDensity M s).trace.re / Fintype.card (ι → α) = 1
      rw [productDensity_trace, Complex.natCast_re]
      exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    · simp only [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ]
  change ENNReal.ofReal (normalizedTraceMap ((product M).toVectorMeasure A)) = _
  rw [h, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl

/-- Every global state has the expected product POVM Born density. -/
theorem product_born_eq_withDensity (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) :
    (product M).born ρ = (Measure.pi (fun i => (M i).traceReference)).withDensity
      (fun s => ENNReal.ofReal
        ((ρ.matrix * tensorMatrix (fun i => (M i).traceDensity (s i))).trace.re)) := by
  apply Measure.ext
  intro A hA
  rw [(product M).born_apply ρ hA, withDensity_apply _ hA]
  have hi := (stateMap ρ).integrable_comp (productDensity_integrable M)
  have hn : ∀ s, 0 ≤ stateMap ρ (productDensity M s) := fun s =>
    QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten ρ.pos (productDensity_pos M s)
  calc
    ENNReal.ofReal ((ρ.matrix * (product M).toVectorMeasure A).trace.re) =
        ENNReal.ofReal (∫ s in A, stateMap ρ (productDensity M s) ∂productReference M) := by
      apply congrArg ENNReal.ofReal
      exact ((stateMap ρ).integral_comp_comm (productDensity_integrable M).integrableOn).trans
        (congrArg (fun B => stateMap ρ B) (product_apply M hA).symm) |>.symm
    _ = _ := ofReal_integral_eq_lintegral_ofReal hi.integrableOn (Filter.Eventually.of_forall hn)

end MeasurablePOVM
end LocalCertification.Quantum
