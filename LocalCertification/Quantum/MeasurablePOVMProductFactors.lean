import LocalCertification.Quantum.MeasurablePOVMProductKernel

/-!
# Recover measurable local factors from a global product POVM kernel

Only the global event effects are assumed measurable. On a cylinder event,
the local effect entries are entries of the global effect with equal fixed
coordinates at all other sites. Thus arbitrary pointwise product factors are
automatically eventwise measurable. No measurable selection or countability
assumption on the outcome spaces is used.
-/
set_option autoImplicit false
open MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace LocalCertification.Quantum

variable {H ι α : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α] [Nonempty α]
  {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

namespace MeasurablePOVM

/-- A cylinder effect contains each local matrix entry literally, since the
other normalized factors contribute identity diagonal entries. -/
theorem product_cylinder_entry (M : ∀ i, MeasurablePOVM (Ω i) α)
    (i : ι) (A : Set (Ω i)) (hA : MeasurableSet A) (a b c : α) :
    (product M).toVectorMeasure
        (Set.univ.pi (Function.update (fun j => (Set.univ : Set (Ω j))) i A))
        (Function.update (fun _ => c) i a) (Function.update (fun _ => c) i b) =
      (M i).toVectorMeasure A a b := by
  classical
  have hm : ∀ j, MeasurableSet
      (Function.update (fun j => (Set.univ : Set (Ω j))) i A j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hA
    · simp [Function.update_of_ne hj]
  rw [product_apply_pi M _ hm]
  change (∏ j, (M j).toVectorMeasure
      (Function.update (fun j => (Set.univ : Set (Ω j))) i A j)
      (Function.update (fun _ => c) i a j) (Function.update (fun _ => c) i b j)) = _
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji, MeasurablePOVM.univ]
  · simp

end MeasurablePOVM

namespace POVMKernel

private theorem eq_of_measurement {X Y I : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [Fintype I] [DecidableEq I] (A B : POVMKernel X Y I)
    (h : ∀ x, A.measurement x = B.measurement x) : A = B := by
  cases A with
  | mk ma ha =>
    cases B with
    | mk mb hb =>
      have he : ma = mb := funext h
      subst mb
      rfl

/-- Local factors of an eventwise measurable product family are themselves
eventwise measurable, even if they were supplied only pointwise. -/
theorem factor_effect_measurable
    (K : POVMKernel H ((i : ι) → Ω i) (ι → α))
    (M : H → ∀ i, MeasurablePOVM (Ω i) α)
    (hprod : ∀ h, K.measurement h = MeasurablePOVM.product (M h))
    (i : ι) (A : Set (Ω i)) (hA : MeasurableSet A) :
    Measurable (fun h => (M h i).toVectorMeasure A) := by
  classical
  let c : α := Classical.choice inferInstance
  have hm : ∀ j, MeasurableSet
      (Function.update (fun j => (Set.univ : Set (Ω j))) i A j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hA
    · simp [Function.update_of_ne hj]
  apply Measurable.of_eval_matrix
  intro a b
  have he := (K.measurable_effect _ (MeasurableSet.univ_pi hm)).eval_matrix
    (i := Function.update (fun _ => c) i a) (j := Function.update (fun _ => c) i b)
  simpa only [hprod, MeasurablePOVM.product_cylinder_entry _ i A hA a b c] using he

/-- Turn pointwise local factors of a measurable global product kernel into
actual local POVM kernels without adding a measurability hypothesis. -/
def factorOfProduct (K : POVMKernel H ((i : ι) → Ω i) (ι → α))
    (M : H → ∀ i, MeasurablePOVM (Ω i) α)
    (hprod : ∀ h, K.measurement h = MeasurablePOVM.product (M h))
    (i : ι) : POVMKernel H (Ω i) α where
  measurement h := M h i
  measurable_effect A hA := factor_effect_measurable K M hprod i A hA

theorem factorOfProduct_measurement
    (K : POVMKernel H ((i : ι) → Ω i) (ι → α))
    (M : H → ∀ i, MeasurablePOVM (Ω i) α)
    (hprod : ∀ h, K.measurement h = MeasurablePOVM.product (M h)) (h : H) (i : ι) :
    (factorOfProduct K M hprod i).measurement h = M h i := rfl

theorem product_factorOfProduct
    (K : POVMKernel H ((i : ι) → Ω i) (ι → α))
    (M : H → ∀ i, MeasurablePOVM (Ω i) α)
    (hprod : ∀ h, K.measurement h = MeasurablePOVM.product (M h)) :
    product (fun i => factorOfProduct K M hprod i) = K := by
  exact eq_of_measurement _ _ (fun h => (hprod h).symm)

/-- The literal global-kernel assumption yields measurable local kernels.
Classical pointwise choice is harmless: the preceding cylinder argument
proves measurability of every chosen factor, rather than assuming it. -/
theorem exists_product_factors
    (K : POVMKernel H ((i : ι) → Ω i) (ι → α))
    (hprod : ∀ h, ∃ M : ∀ i, MeasurablePOVM (Ω i) α,
      K.measurement h = MeasurablePOVM.product M) :
    ∃ F : ∀ i, POVMKernel H (Ω i) α, product F = K := by
  classical
  let M := fun h => Classical.choose (hprod h)
  have hp : ∀ h, K.measurement h = MeasurablePOVM.product (M h) :=
    fun h => Classical.choose_spec (hprod h)
  exact ⟨fun i => factorOfProduct K M hp i, product_factorOfProduct K M hp⟩

end POVMKernel
end LocalCertification.Quantum
