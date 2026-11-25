import LocalCertification.Quantum.MeasurablePOVMKernel
import LocalCertification.Quantum.MeasurablePOVMFinite
import LocalCertification.Quantum.MeasurablePOVMProduct
import LocalCertification.Quantum.BornKernel

/-!
# Exact finite and product-basis embeddings

The existing physical product-basis POVMs are the actual products of their local
finite embeddings. Their eventwise Born kernels equal the existing source kernels.
-/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
noncomputable section
namespace LocalCertification.Quantum

namespace POVMKernel
variable {H O I : Type*} [MeasurableSpace H] [MeasurableSpace O]
  [Fintype O] [MeasurableSingletonClass O] [Fintype I] [DecidableEq I]

/-- Finite POVM families embed whenever each original finite effect is measurable. -/
def ofFinite (M : H → QIT.POVM O I)
    (hM : ∀ x, Measurable (fun h => (M h).effects x)) : POVMKernel H O I where
  measurement h := MeasurablePOVM.ofFinite (M h)
  measurable_effect A hA := by
    classical
    apply Measurable.of_eval_matrix
    intro i j
    simp_rw [MeasurablePOVM.ofFinite_apply _ hA]
    simp only [Matrix.sum_apply]
    apply Finset.measurable_sum
    intro x _
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx] using (hM x).eval_matrix (i := i) (j := j)
    · simp only [Set.indicator_of_notMem hx]
      exact measurable_const

theorem bornKernel_ofFinite_apply [DecidableEq O] (M : H → QIT.POVM O I)
    (hM : ∀ x, Measurable (fun h => (M h).effects x)) (ρ : QIT.State I) (h : H) :
    (ofFinite M hM).bornKernel ρ h = povmBornMeasure (M h) ρ :=
  MeasurablePOVM.born_ofFinite (M h) ρ
end POVMKernel

namespace MeasurablePOVM
variable {O I : Type*} [MeasurableSpace O] [Fintype O] [MeasurableSingletonClass O]
  [Fintype I] [DecidableEq I]

private theorem eq_of_singletons (M N : MeasurablePOVM O I)
    (h : ∀ x, M.toVectorMeasure {x} = N.toVectorMeasure {x}) : M = N := by
  have hvec : M.toVectorMeasure = N.toVectorMeasure := by
    apply VectorMeasure.ext
    intro A _
    have he : A = ⋃ x : A, ({(x : O)} : Set O) := by ext x; simp
    have hm : ∀ x : A, MeasurableSet ({(x : O)} : Set O) := fun _ => measurableSet_singleton _
    have hd : Pairwise (fun x y : A => Disjoint ({(x : O)} : Set O) {(y : O)}) := by
      intro x y hxy
      exact Set.disjoint_singleton.mpr (fun he => hxy (Subtype.ext he))
    rw [he, VectorMeasure.of_disjoint_iUnion hm hd, VectorMeasure.of_disjoint_iUnion hm hd]
    exact tsum_congr (fun x => h x)
  cases M
  cases N
  cases hvec
  rfl

/-- A singleton of a product outcome is the tensor of all local singleton effects. -/
theorem product_singleton {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Nonempty α]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (M : ∀ i, MeasurablePOVM (Ω i) α) (s : (i : ι) → Ω i) :
    (product M).toVectorMeasure {s} = tensorMatrix (fun i => (M i).toVectorMeasure {s i}) := by
  have he : ({s} : Set ((i : ι) → Ω i)) = Set.univ.pi (fun i => {s i}) := by
    ext t
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
    exact funext_iff
  rw [he, product_apply_pi M _ (fun _ => measurableSet_singleton _)]

/-- The actual product of the local source basis measurements, on the original qudit labels. -/
def productBasis (d n : ℕ) [NeZero d] (U : Fin n → CertificationGaussian.LocalUnitary d) :
    MeasurablePOVM (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) :=
  product (fun i => ofFinite (basisPOVM (U i)))

theorem productBasis_singleton (d n : ℕ) [NeZero d]
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    (productBasis d n U).toVectorMeasure {x} = (productBasisPOVM d n U).effects x := by
  exact (product_singleton (fun i => ofFinite (basisPOVM (U i))) x).trans
    (by simp only [ofFinite_singleton, productBasisPOVM_effect])

/-- Equality of actual matrix measures, not merely equality of named probabilities. -/
theorem productBasis_eq_ofFinite (d n : ℕ) [NeZero d]
    (U : Fin n → CertificationGaussian.LocalUnitary d) :
    productBasis d n U = ofFinite (productBasisPOVM d n U) := by
  apply eq_of_singletons
  intro x
  rw [productBasis_singleton, ofFinite_singleton]

theorem productBasis_born (d n : ℕ) [NeZero d]
    (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (productBasis d n U).born ρ = productBornMeasure d n U ρ := by
  rw [productBasis_eq_ofFinite, born_ofFinite]
  rfl
end MeasurablePOVM

namespace POVMKernel
/-- Each physical product-basis effect is measurable in the full continuous setting. -/
theorem productBasis_effect_measurable (d n : ℕ) (x : CertificationGaussian.QuditIndex d n) :
    Measurable (fun U : Fin n → CertificationGaussian.LocalUnitary d =>
      (productBasisPOVM d n U).effects x) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp_rw [productBasisPOVM_effect, tensorMatrix, basisPOVM_effect_rankOne, QIT.rankOneMatrix_apply]
  apply Continuous.measurable
  have he (i : Fin n) (a b : Fin d) : Continuous
      (fun U : Fin n → CertificationGaussian.LocalUnitary d => (U i).val a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp
      ((continuous_subtype_val : Continuous (fun V : CertificationGaussian.LocalUnitary d => V.val)).comp
        (continuous_apply i)))
  exact continuous_finsetProd _ (fun i _ => (he i (a i) (x i)).mul (he i (b i) (x i)).star)

/-- The original continuous product settings as a general measurable POVM family. -/
def productBasis (d n : ℕ) : POVMKernel (Fin n → CertificationGaussian.LocalUnitary d)
    (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) :=
  ofFinite (productBasisPOVM d n) (productBasis_effect_measurable d n)

theorem productBasis_measurement (d n : ℕ) [NeZero d]
    (U : Fin n → CertificationGaussian.LocalUnitary d) :
    (productBasis d n).measurement U = MeasurablePOVM.productBasis d n U :=
  (MeasurablePOVM.productBasis_eq_ofFinite d n U).symm

/-- Exact kernel equality preserves every history law built from the existing source kernel. -/
theorem bornKernel_productBasis (d n : ℕ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    (productBasis d n).bornKernel ρ = productBornKernel d n ρ := by
  apply Kernel.ext
  intro U
  exact bornKernel_ofFinite_apply (productBasisPOVM d n) (productBasis_effect_measurable d n) ρ U

theorem bornKernel_productBasis_reindex {H : Type*} [MeasurableSpace H]
    (d n : ℕ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting) :
    ((productBasis d n).reindex setting hm).bornKernel ρ =
      controlledProductBornKernel d n ρ setting hm := by
  apply Kernel.ext
  intro h
  exact bornKernel_ofFinite_apply (productBasisPOVM d n) (productBasis_effect_measurable d n) ρ (setting h)
end POVMKernel
end LocalCertification.Quantum
