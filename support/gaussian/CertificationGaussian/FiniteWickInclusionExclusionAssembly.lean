import CertificationGaussian.FiniteWickInclusionExclusionCompletion

noncomputable section
open Finset MvPolynomial
open scoped BigOperators
namespace CertificationGaussian

/-- A deterministic extension of each two-by-two partial matching. -/
def localWickPermutation (s : Finset LocalWickEdge) : Equiv.Perm (Fin 2) :=
  if (0,1) ∈ s ∨ (1,0) ∈ s then Equiv.swap 0 1 else Equiv.refl _

/-- The chosen extension has exactly the selected edges on the selected domain. -/
theorem localWickPermutation_edges (s : Finset LocalWickEdge)
    (hs : s ∈ localWickContractions) (a b : Fin 2) :
    (a,b) ∈ s ↔ a ∈ s.image Prod.fst ∧ localWickPermutation s a = b := by
  have h : ∀ s ∈ localWickContractions, ∀ a b : Fin 2,
      (a,b) ∈ s ↔ a ∈ s.image Prod.fst ∧ localWickPermutation s a = b := by decide
  exact h s hs a b

/-- Every local normal-order summand is the signed deleted monomial of its partial matching. -/
theorem localWickContractionPolynomial_deletion {I : Type*} [DecidableEq I]
    (i j : Fin 2 → I) (s : Finset LocalWickEdge) (hs : s ∈ localWickContractions) :
    localWickContractionPolynomial i j s = C ((-1 : ℂ) ^ s.card) *
      wickDeletionPolynomial (s.image Prod.fst) (localWickPermutation s) i j := by
  have h0 : ({(0 : Fin 2), 1} : Finset (Fin 2)) \ {0} = {1} := by decide
  have h1 : ({(0 : Fin 2), 1} : Finset (Fin 2)) \ {1,0} = ∅ := by decide
  simp only [localWickContractions, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [localWickContractionPolynomial, wickDeletionPolynomial, localWickPermutation,
      Fin.univ_succ, h0, h1, Fin.prod_univ_two, Equiv.swap_apply_def] <;> ring

/-- A choice of one genuine normal-order contraction term in each of four blocks. -/
abbrev FourWickChoice := Fin 4 → {s : Finset LocalWickEdge // s ∈ localWickContractions}

/-- Selected global bar positions of a four-block expansion term. -/
def fourWickChoiceDomain (q : FourWickChoice) : Finset FourWickPosition :=
  univ.filter (fun a => a.2 ∈ (q a.1).1.image Prod.fst)

/-- Block-preserving reference matching extending all selected contraction edges. -/
def fourWickChoicePermutation (q : FourWickChoice) : Equiv.Perm FourWickPosition :=
  Equiv.prodCongrRight (fun b => localWickPermutation (q b).1)

/-- Signed coefficient of an actual four-block expansion term. -/
def fourWickChoiceSign (q : FourWickChoice) : ℂ :=
  ∏ b, (-1 : ℂ) ^ (q b).1.card

/-- Reassemble the uncontracted and delta factors before taking expectation. -/
theorem fourWickChoice_polynomial {I : Type*} [DecidableEq I]
    (i j : FourWickPosition → I) (q : FourWickChoice) :
    (∏ b, localWickContractionPolynomial (fun a => i (b,a)) (fun a => j (b,a)) (q b).1) =
      C (fourWickChoiceSign q) *
        wickDeletionPolynomial (fourWickChoiceDomain q) (fourWickChoicePermutation q) i j := by
  simp_rw [localWickContractionPolynomial_deletion _ _ _ (q _).2]
  rw [Finset.prod_mul_distrib, ← map_prod]
  change C (fourWickChoiceSign q) * _ = C (fourWickChoiceSign q) * _
  apply congrArg (fun P => C (fourWickChoiceSign q) * P)
  simp only [wickDeletionPolynomial, fourWickChoiceDomain, fourWickChoicePermutation,
    Fintype.prod_prod_type, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.prodCongrRight_apply]

/-- Expand the actual product of four normal quartics into its finite choices. -/
theorem fourNormalQuartics_finite_expansion {I : Type*} [DecidableEq I]
    (i j : FourWickPosition → I) :
    (∏ b : Fin 4, gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1))) =
      ∑ q : FourWickChoice, C (fourWickChoiceSign q) *
        wickDeletionPolynomial (fourWickChoiceDomain q) (fourWickChoicePermutation q) i j := by
  have h b := gaussianNormalQuartic_finite_expansion (fun a => i (b,a)) (fun a => j (b,a))
  simp_rw [h]
  have hs b : (∑ s ∈ localWickContractions,
      localWickContractionPolynomial (fun a => i (b,a)) (fun a => j (b,a)) s) =
      ∑ s : {s : Finset LocalWickEdge // s ∈ localWickContractions},
        localWickContractionPolynomial (fun a => i (b,a)) (fun a => j (b,a)) s.1 :=
    (Finset.sum_coe_sort _ _).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl (fun q _ => fourWickChoice_polynomial i j q)

/-- Integrating each genuine finite expansion term uses only ordinary Wick on undeleted positions. -/
theorem fourNormalQuartics_completion_expansion {I : Type*} [Fintype I] [DecidableEq I]
    (i j : FourWickPosition → I) :
    complexGaussianPolyExpectation
      (∏ b : Fin 4, gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1))) =
      ∑ q : FourWickChoice, fourWickChoiceSign q *
        ∑ π : WickCompletion (fourWickChoiceDomain q) (fourWickChoicePermutation q),
          ∏ a, if i a = j (π.1 a) then (1 : ℂ) else 0 := by
  rw [fourNormalQuartics_finite_expansion, complexGaussianPolyExpectation_sum]
  simp_rw [complexGaussianPolyExpectation_C_mul, wickDeletionPolynomial_expectation]

end CertificationGaussian
