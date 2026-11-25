import CertificationGaussian.FiniteWickInclusionExclusionExpansion

noncomputable section
open Finset MvPolynomial
open scoped BigOperators
namespace CertificationGaussian

/-- Ordinary Wick on any finite labelled position type, derived only from balanced monomial Wick. -/
theorem finiteWick_monomial {A I : Type*} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] (i j : A → I) :
    complexGaussianPolyExpectation
      ((∏ a, gaussianBarZPolynomial (i a)) * ∏ a, gaussianZPolynomial (j a)) =
      ∑ π : Equiv.Perm A, ∏ a, if i a = j (π a) then (1 : ℂ) else 0 := by
  let e := Fintype.equivFin A
  have h := complexGaussian_balanced_wick (Fintype.card A)
    (fun a => i (e.symm a)) (fun a => j (e.symm a))
  unfold gaussianBalancedMonomial gaussianMixedMonomial complexGaussianPairingSum at h
  rw [e.symm.prod_comp (fun a => gaussianBarZPolynomial (i a)),
    e.symm.prod_comp (fun a => gaussianZPolynomial (j a))] at h
  rw [h]
  rw [← e.permCongr.sum_comp]
  apply Finset.sum_congr rfl
  intro π _
  rw [← e.prod_comp]
  simp

/-- A full matching extending selected edges, with the extension condition on labelled positions. -/
abbrev WickCompletion {A : Type*} [DecidableEq A] (s : Finset A) (τ : Equiv.Perm A) :=
  {π : Equiv.Perm A // ∀ a : (s : Set A), π a = τ a}

instance {A : Type*} [Fintype A] [DecidableEq A] (s : Finset A) (τ : Equiv.Perm A) :
    Fintype (WickCompletion s τ) := by
  classical
  unfold WickCompletion
  infer_instance

/-- Deleting selected edges gives a bijection with matchings of the uncontracted positions. -/
def wickCompletionEquiv {A : Type*} [DecidableEq A] (s : Finset A) (τ : Equiv.Perm A) :
    WickCompletion s τ ≃ Equiv.Perm {a : A // a ∉ s} :=
  (show WickCompletion s τ ≃ {σ : Equiv.Perm A // ∀ a : (s : Set A), σ a = a} from
    { toFun := fun π => ⟨π.1.trans τ.symm, fun a => by simp [π.2 a]⟩
      invFun := fun σ => ⟨σ.1.trans τ, fun a => by simp [σ.2 a]⟩
      left_inv := fun π => by apply Subtype.ext; ext a; simp
      right_inv := fun σ => by apply Subtype.ext; ext a; simp }).trans
    (Equiv.Set.compl (Equiv.refl (s : Set A)))

/-- The deleted matching sends an uncontracted position to the inverse-reference image of its partner. -/
theorem wickCompletionEquiv_apply {A : Type*} [DecidableEq A]
    (s : Finset A) (τ : Equiv.Perm A) (π : WickCompletion s τ) (a : {a : A // a ∉ s}) :
    ((wickCompletionEquiv s τ π a : {a : A // a ∉ s}) : A) = τ.symm (π.1 a) := rfl

/-- Ordinary Wick after deleting the selected contraction edges, reindexed by full completions. -/
theorem finiteWick_deleted_monomial {A I : Type*} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] (s : Finset A) (τ : Equiv.Perm A) (i j : A → I) :
    complexGaussianPolyExpectation
      ((∏ a : {a : A // a ∉ s}, gaussianBarZPolynomial (i a)) *
        ∏ a : {a : A // a ∉ s}, gaussianZPolynomial (j (τ a))) =
      ∑ π : WickCompletion s τ,
        ∏ a : {a : A // a ∉ s}, if i a = j (π.1 a) then (1 : ℂ) else 0 := by
  rw [finiteWick_monomial]
  rw [← (wickCompletionEquiv s τ).sum_comp]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.prod_congr rfl
  intro a _
  simp only [wickCompletionEquiv_apply, Equiv.apply_symm_apply]

/-- A selected partial matching contributes its delta factors times the undeleted monomial. -/
def finiteWickContractedPolynomial {A I : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq I] (s : Finset A) (τ : Equiv.Perm A) (i j : A → I) :
    MvPolynomial (Fin 2 × I) ℂ :=
  C (∏ a : (s : Set A), if i a = j (τ a) then (1 : ℂ) else 0) *
    ((∏ a : {a : A // a ∉ s}, gaussianBarZPolynomial (i a)) *
      ∏ a : {a : A // a ∉ s}, gaussianZPolynomial (j (τ a)))

/-- The moment of a contracted monomial counts exactly the complete matchings extending it. -/
theorem finiteWick_contracted_monomial {A I : Type*} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] (s : Finset A) (τ : Equiv.Perm A) (i j : A → I) :
    complexGaussianPolyExpectation (finiteWickContractedPolynomial s τ i j) =
      ∑ π : WickCompletion s τ, ∏ a, if i a = j (π.1 a) then (1 : ℂ) else 0 := by
  rw [finiteWickContractedPolynomial, complexGaussianPolyExpectation_C_mul,
    finiteWick_deleted_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  conv_rhs => rw [← Fintype.prod_subtype_mul_prod_subtype (fun a => a ∈ s)]
  congr 1
  simp only [π.2]
  congr 1
  ext a
  simp

/-- A deleted monomial written as one factor per original labelled position. -/
def wickDeletionPolynomial {A I : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq I] (s : Finset A) (τ : Equiv.Perm A) (i j : A → I) :
    MvPolynomial (Fin 2 × I) ℂ :=
  ∏ a, if a ∈ s then gaussianDeltaPolynomial (i a) (j (τ a))
    else gaussianBarZPolynomial (i a) * gaussianZPolynomial (j (τ a))

theorem finiteWickContractedPolynomial_eq_deletion {A I : Type*}
    [Fintype A] [DecidableEq A] [DecidableEq I]
    (s : Finset A) (τ : Equiv.Perm A) (i j : A → I) :
    finiteWickContractedPolynomial s τ i j = wickDeletionPolynomial s τ i j := by
  unfold wickDeletionPolynomial
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun a => a ∈ s)]
  simp only [Subtype.property, ite_eq_left,
    show ∀ a : {a : A // a ∉ s}, ¬(a.1 ∈ s) from fun a => a.2, ite_false,
    Finset.prod_mul_distrib, gaussianDeltaPolynomial, ← map_prod]
  unfold finiteWickContractedPolynomial
  congr 2
  congr 1
  ext a
  simp

theorem wickDeletionPolynomial_expectation {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (s : Finset A) (τ : Equiv.Perm A) (i j : A → I) :
    complexGaussianPolyExpectation (wickDeletionPolynomial s τ i j) =
      ∑ π : WickCompletion s τ, ∏ a, if i a = j (π.1 a) then (1 : ℂ) else 0 := by
  rw [← finiteWickContractedPolynomial_eq_deletion, finiteWick_contracted_monomial]

end CertificationGaussian
