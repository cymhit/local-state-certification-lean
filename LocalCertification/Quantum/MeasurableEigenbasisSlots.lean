import LocalCertification.Quantum.MeasurableGramSchmidt
import Mathlib.Data.Finset.Sort

/-! Compression of nonzero Gram–Schmidt residuals in ascending slot order.
All assignments of slots are measurable on arbitrary input measurable spaces. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory InnerProductSpace Module Set
namespace LocalCertification.Quantum
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] {m : ℕ}
local notation "E" => EuclideanSpace ℂ I

/-- The increasing bijection to the retained positions of a spanning list. -/
def activeGramSchmidtEquiv (v : Fin m → E) (hv : Submodule.span ℂ (range v) = ⊤) :
    Fin (Fintype.card I) ≃o nonzeroSlots (gramSchmidtNormed ℂ v) :=
  (nonzeroSlots (gramSchmidtNormed ℂ v)).orderIsoOfFin (card_nonzeroGramSchmidt v hv)

/-- The deterministic slot of the `i`-th retained nonzero residual. -/
def activeGramSchmidtSlot (v : Fin m → E) (hv : Submodule.span ℂ (range v) = ⊤)
    (i : Fin (Fintype.card I)) : Fin m :=
  activeGramSchmidtEquiv v hv i

/-- On a fixed support stratum the slot selection is constant. -/
theorem activeGramSchmidtSlot_eq_on_support (v w : Fin m → E)
    (hv : Submodule.span ℂ (range v) = ⊤) (hw : Submodule.span ℂ (range w) = ⊤)
    (h : nonzeroSlots (gramSchmidtNormed ℂ v) = nonzeroSlots (gramSchmidtNormed ℂ w))
    (i : Fin (Fintype.card I)) : activeGramSchmidtSlot v hv i = activeGramSchmidtSlot w hw i := by
  have congSlot (S T : Finset (Fin m)) (hS : S.card = Fintype.card I)
      (hT : T.card = Fintype.card I) (heq : S = T) :
      ((S.orderIsoOfFin hS i).val) = ((T.orderIsoOfFin hT i).val) := by
    subst T
    rfl
  exact congSlot _ _ _ _ h

theorem measurable_activeGramSchmidtSlot (v : Ω → Fin m → E)
    (hv : ∀ k, Measurable (v · k)) (hspan : ∀ s, Submodule.span ℂ (range (v s)) = ⊤)
    (i : Fin (Fintype.card I)) : Measurable (fun s => activeGramSchmidtSlot (v s) (hspan s) i) := by
  classical
  let w := fun s => gramSchmidtNormed ℂ (v s)
  have hw : ∀ k, Measurable (w · k) := measurable_gramSchmidtNormed v hv
  apply measurable_to_countable'
  intro k
  let U (S : Finset (Fin m)) : Set Ω :=
    if ∃ t, nonzeroSlots (w t) = S ∧ activeGramSchmidtSlot (v t) (hspan t) i = k
    then {s | nonzeroSlots (w s) = S} else ∅
  have hU (S : Finset (Fin m)) : MeasurableSet (U S) := by
    dsimp only [U]
    split_ifs
    · exact measurableSet_nonzeroSlots w hw S
    · exact MeasurableSet.empty
  convert MeasurableSet.iUnion hU using 1
  ext s
  change activeGramSchmidtSlot (v s) (hspan s) i = k ↔ s ∈ ⋃ S, U S
  simp only [Set.mem_iUnion]
  constructor
  · intro h
    refine ⟨nonzeroSlots (w s), ?_⟩
    simp only [U, ite_eq_left (show ∃ t, nonzeroSlots (w t) = nonzeroSlots (w s) ∧
      activeGramSchmidtSlot (v t) (hspan t) i = k from ⟨s, rfl, h⟩), Set.mem_ofPred_eq]
  · rintro ⟨S,hs⟩
    dsimp only [U] at hs
    split_ifs at hs with h
    · obtain ⟨t, ht, hk⟩ := h
      exact (activeGramSchmidtSlot_eq_on_support _ _ _ _ (hs.trans ht.symm) i).trans hk
    · exact hs.elim

/-- Evaluation of a finite family at a measurable slot, including a slot
which changes when an eigenvalue multiplicity or pivot changes. -/
theorem measurable_at_slot {κ V : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (v : Ω → κ → V) (hv : ∀ k, Measurable (v · k)) (slot : Ω → κ) (hs : Measurable slot) :
    Measurable (fun s => v s (slot s)) := by
  classical
  have he (s : Ω) : v s (slot s) = ∑ k, if slot s = k then v s k else 0 := by simp
  simp_rw [he]
  exact Finset.measurable_sum _ (fun k _ =>
    Measurable.ite (hs (measurableSet_singleton k)) (hv k) measurable_const)

/-- The selected, normalized vectors form a complete orthonormal basis. -/
def selectedGramSchmidtBasis (v : Fin m → E) (hv : Submodule.span ℂ (range v) = ⊤) :
    OrthonormalBasis (Fin (Fintype.card I)) ℂ E := by
  let w := gramSchmidtNormed ℂ v
  have h : Submodule.span ℂ (range (fun i : nonzeroSlots w => w i)) = ⊤ := by
    rw [span_nonzeroSlots, InnerProductSpace.span_gramSchmidtNormed_range,
      InnerProductSpace.span_gramSchmidt, hv]
  exact (OrthonormalBasis.mk (orthonormal_nonzeroGramSchmidt v) h.ge).reindex
    (activeGramSchmidtEquiv v hv).toEquiv.symm

@[simp] theorem selectedGramSchmidtBasis_apply (v : Fin m → E)
    (hv : Submodule.span ℂ (range v) = ⊤) (i : Fin (Fintype.card I)) :
    selectedGramSchmidtBasis v hv i = gramSchmidtNormed ℂ v (activeGramSchmidtSlot v hv i) := by
  simp [selectedGramSchmidtBasis, activeGramSchmidtSlot]

theorem measurable_selectedGramSchmidtBasis (v : Ω → Fin m → E)
    (hv : ∀ k, Measurable (v · k)) (hspan : ∀ s, Submodule.span ℂ (range (v s)) = ⊤)
    (i : Fin (Fintype.card I)) : Measurable (fun s => selectedGramSchmidtBasis (v s) (hspan s) i) := by
  simp_rw [selectedGramSchmidtBasis_apply]
  exact measurable_at_slot _ (measurable_gramSchmidtNormed v hv) _ (measurable_activeGramSchmidtSlot v hv hspan i)

end LocalCertification.Quantum

