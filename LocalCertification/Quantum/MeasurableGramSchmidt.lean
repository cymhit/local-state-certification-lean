import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Spectrum
import LocalCertification.Quantum.MeasurablePOVMDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! Fixed-order Gram–Schmidt for a measurable spanning list of eigenvectors.
The nonzero normalized residuals are selected in their original finite order;
changes of pivot occur on measurable strata. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Module Set
open scoped BigOperators ComplexOrder

namespace LocalCertification.Quantum
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] {m : ℕ}
local notation "E" => EuclideanSpace ℂ I

/-- Each residual, including a zero residual, is a measurable function of the input list. -/
theorem measurable_gramSchmidt (f : Ω → Fin m → E) (hf : ∀ k, Measurable (f · k))
    (k : Fin m) : Measurable (fun s => gramSchmidt ℂ (f s) k) := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    simp_rw [gramSchmidt_def ℂ _ k, Submodule.starProjection_singleton]
    apply (hf k).sub (Finset.measurable_sum _ ?_)
    intro i hi
    have hu := ih i (Finset.mem_Iio.mp hi)
    have hz : Measurable (fun s => inner ℂ (gramSchmidt ℂ (f s) i) (f s k)) :=
      continuous_inner.measurable.comp (hu.prodMk (hf k))
    exact (hz.div (Complex.measurable_ofReal.comp (hu.norm.pow_const 2))).smul hu

theorem measurable_gramSchmidtNormed (f : Ω → Fin m → E) (hf : ∀ k, Measurable (f · k))
    (k : Fin m) : Measurable (fun s => gramSchmidtNormed ℂ (f s) k) := by
  have hr := measurable_gramSchmidt f hf k
  exact (Complex.measurable_ofReal.comp hr.norm).inv.smul hr

/-- Orthogonal eigenspaces do not mix when previous residuals are subtracted. -/
theorem gramSchmidtNormed_mem_eigenspace (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (mu : Fin m → ℂ) (v : Fin m → E) (hv : ∀ k, v k ∈ End.eigenspace T (mu k)) (k : Fin m) :
    gramSchmidtNormed ℂ v k ∈ End.eigenspace T (mu k) := by
  have hres (j : Fin m) : gramSchmidt ℂ v j ∈ End.eigenspace T (mu j) := by
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      rw [gramSchmidt_def]
      apply Submodule.sub_mem _ (hv j)
      apply Submodule.sum_mem
      intro i hi
      rw [Submodule.starProjection_singleton]
      have hir := ih i (Finset.mem_Iio.mp hi)
      by_cases he : mu i = mu j
      · exact Submodule.smul_mem _ _ (he ▸ hir)
      · have hz : inner ℂ (gramSchmidt ℂ v i) (v j) = 0 :=
          hT.orthogonalFamily_eigenspaces he ⟨_,hir⟩ ⟨_,hv j⟩
        simp [hz]
  exact Submodule.smul_mem _ _ (hres k)

/-- Positions retained when zero residuals are skipped. -/
def nonzeroSlots (v : Fin m → E) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => v i ≠ 0)

@[simp] theorem mem_nonzeroSlots (v : Fin m → E) (k : Fin m) :
    k ∈ nonzeroSlots v ↔ v k ≠ 0 := by classical simp [nonzeroSlots]

theorem measurableSet_nonzeroSlots (v : Ω → Fin m → E) (hv : ∀ i, Measurable (v · i))
    (S : Finset (Fin m)) : MeasurableSet {s | nonzeroSlots (v s) = S} := by
  classical
  have hs (i : Fin m) : MeasurableSet {s | (v s i ≠ 0 ↔ i ∈ S)} := by
    have hz : MeasurableSet {s | v s i = 0} := measurableSet_eq_fun (hv i) measurable_const
    by_cases h : i ∈ S
    · simp only [h, iff_true]
      exact hz.compl
    · simpa only [h, iff_false, not_not] using hz
  convert MeasurableSet.iInter hs using 1
  ext s
  simp [Finset.ext_iff]

theorem span_nonzeroSlots (v : Fin m → E) :
    Submodule.span ℂ (range (fun i : nonzeroSlots v => v i)) = Submodule.span ℂ (range v) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i,rfl⟩; exact ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases h : v i = 0
    · rw [h]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i,(mem_nonzeroSlots v i).mpr h⟩,rfl⟩

theorem orthonormal_nonzeroGramSchmidt (v : Fin m → E) :
    Orthonormal ℂ (fun i : nonzeroSlots (gramSchmidtNormed ℂ v) => gramSchmidtNormed ℂ v i) := by
  let e (i : nonzeroSlots (gramSchmidtNormed ℂ v)) :
      {k | gramSchmidtNormed ℂ v k ≠ 0} := ⟨i,(mem_nonzeroSlots _ _).mp i.prop⟩
  exact (gramSchmidtNormed_orthonormal' v).comp e
    (fun a b h => Subtype.ext (congrArg (fun i : {k | gramSchmidtNormed ℂ v k ≠ 0} => i.val) h))

/-- The number of retained positions in a spanning list equals the ambient dimension. -/
theorem card_nonzeroGramSchmidt (v : Fin m → E) (hspan : Submodule.span ℂ (range v) = ⊤) :
    (nonzeroSlots (gramSchmidtNormed ℂ v)).card = Fintype.card I := by
  let w := gramSchmidtNormed ℂ v
  have h : Submodule.span ℂ (range (fun i : nonzeroSlots w => w i)) = ⊤ := by
    rw [span_nonzeroSlots, InnerProductSpace.span_gramSchmidtNormed_range,
      InnerProductSpace.span_gramSchmidt, hspan]
  let B := Basis.mk (orthonormal_nonzeroGramSchmidt v).linearIndependent h.ge
  simpa only [finrank_euclideanSpace, Fintype.card_coe] using (finrank_eq_card_basis B).symm

end LocalCertification.Quantum

