import CertificationGaussian.FiniteWickInclusionExclusionFiber

noncomputable section
open Finset MvPolynomial
open scoped BigOperators
namespace CertificationGaussian

/-- Completing the selected global edges is exactly compatibility in each of the four blocks. -/
theorem fourWickChoice_completion_iff (q : FourWickChoice) (π : Equiv.Perm FourWickPosition) :
    (∀ a : (fourWickChoiceDomain q : Set FourWickPosition),
      π a = fourWickChoicePermutation q a) ↔
      ∀ b, (q b).1 ⊆ localWickInternalEdges π b := by
  constructor
  · intro h b e he
    have hm : (b,e.1) ∈ fourWickChoiceDomain q := by
      simp only [fourWickChoiceDomain, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_image.mpr ⟨e,he,rfl⟩
    have hp := h ⟨(b,e.1),hm⟩
    have ht := (localWickPermutation_edges (q b).1 (q b).2 e.1 e.2).mp he
    simpa [localWickInternalEdges, fourWickChoicePermutation, ht.2] using hp
  · intro h a
    have hm : a.1.2 ∈ (q a.1.1).1.image Prod.fst := by
      simpa [fourWickChoiceDomain] using a.2
    obtain ⟨e,he,hea⟩ := Finset.mem_image.mp hm
    have hp := (Finset.mem_filter.mp (h a.1.1 he)).2
    have ht := (localWickPermutation_edges (q a.1.1).1 (q a.1.1).2 e.1 e.2).mp he
    have ha : a.1 = (a.1.1,e.1) := Prod.ext rfl hea.symm
    rw [ha]
    simpa [fourWickChoicePermutation, ht.2] using hp

/-- Reindex completion sums as all complete matchings with an explicit finite compatibility filter. -/
theorem fourWick_completion_sum (q : FourWickChoice) (w : Equiv.Perm FourWickPosition → ℂ) :
    (∑ π : WickCompletion (fourWickChoiceDomain q) (fourWickChoicePermutation q), w π.1) =
      ∑ π : Equiv.Perm FourWickPosition,
        if ∀ b, (q b).1 ⊆ localWickInternalEdges π b then w π else 0 := by
  classical
  change (∑ π : {π : Equiv.Perm FourWickPosition //
    ∀ a : (fourWickChoiceDomain q : Set FourWickPosition),
      π a = fourWickChoicePermutation q a}, w π.1) = _
  rw [← Finset.sum_subtype (univ.filter (fun π : Equiv.Perm FourWickPosition =>
    ∀ a : (fourWickChoiceDomain q : Set FourWickPosition),
      π a = fourWickChoicePermutation q a)) (by intro π; simp)]
  simp only [Finset.sum_filter, fourWickChoice_completion_iff]

/-- All four local internal edge sets are empty precisely for the original no-internal matchings. -/
theorem localWickInternalEdges_all_empty_iff (π : Equiv.Perm FourWickPosition) :
    (∀ b, localWickInternalEdges π b = ∅) ↔ π ∈ fourBlockDerangements := by
  simp only [fourBlockDerangements, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h a ha
    have he : (a.2,(π a).2) ∈ localWickInternalEdges π a.1 := by
      simp only [localWickInternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Prod.ext ha rfl
    rw [h] at he
    exact Finset.notMem_empty _ he
  · intro h b
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hp := (Finset.mem_filter.mp he).2
    have heq : (π (b,e.1)).1 = b := congrArg (fun x : FourWickPosition => x.1) hp
    exact h (b,e.1) heq

/-- The coefficient of each full matching in the actual four-block expansion.
The four local subset fibers multiply to the global alternating-subset coefficient. -/
theorem fourWick_expansion_coefficient (π : Equiv.Perm FourWickPosition) :
    (∑ q : FourWickChoice,
      if ∀ b, (q b).1 ⊆ localWickInternalEdges π b then fourWickChoiceSign q else 0) =
      ∑ s ∈ (fourWickInternalPositions π).powerset, (-1 : ℂ) ^ s.card := by
  classical
  unfold fourWickChoiceSign
  have hp (q : FourWickChoice) :
      (if ∀ b, (q b).1 ⊆ localWickInternalEdges π b then
        ∏ b, (-1 : ℂ) ^ (q b).1.card else 0) =
      ∏ b, if (q b).1 ⊆ localWickInternalEdges π b then (-1 : ℂ) ^ (q b).1.card else 0 :=
    by
      by_cases hc : ∀ b, (q b).1 ⊆ localWickInternalEdges π b
      · simp [hc]
      · rw [ite_eq_right hc]
        symm
        push Not at hc
        obtain ⟨b,hb⟩ := hc
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun (b : Fin 4)
    (s : {s : Finset LocalWickEdge // s ∈ localWickContractions}) =>
      if s.1 ⊆ localWickInternalEdges π b then (-1 : ℂ) ^ s.1.card else 0)]
  have h b : (∑ s : {s : Finset LocalWickEdge // s ∈ localWickContractions},
      if s.1 ⊆ localWickInternalEdges π b then (-1 : ℂ) ^ s.1.card else 0) =
      if localWickInternalEdges π b = ∅ then 1 else 0 := by
    rw [Finset.sum_coe_sort localWickContractions
      (fun s => if s ⊆ localWickInternalEdges π b then (-1 : ℂ) ^ s.card else 0)]
    exact localWick_expansion_coefficient π b
  simp_rw [h]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one, localWickInternalEdges_all_empty_iff,
    fourWick_matching_coefficient]

/-- The actual expansion coefficient is reindexed by the sign-preserving global edge-subset bijection. -/
theorem fourWick_expansion_coefficient_via_fiber (π : Equiv.Perm FourWickPosition) :
    (∑ q : FourWickChoice,
      if ∀ b, (q b).1 ⊆ localWickInternalEdges π b then fourWickChoiceSign q else 0) =
      ∑ s ∈ (fourWickInternalPositions π).powerset, (-1 : ℂ) ^ s.card := by
  classical
  calc
    _ = ∑ q : FourWickCompatibleChoice π, fourWickChoiceSign q.1 := by
      rw [← Finset.sum_subtype
        (univ.filter (fun q : FourWickChoice => ∀ b, (q b).1 ⊆ localWickInternalEdges π b))
        (by intro q; simp)]
      simp only [Finset.sum_filter]
    _ = ∑ s : FourWickInternalSubset π, (-1 : ℂ) ^ s.1.card := by
      rw [← (fourWickExpansionFiberEquiv π).sum_comp]
      exact Finset.sum_congr rfl (fun q _ => fourWickExpansionFiberEquiv_sign π q)
    _ = _ := by
      exact (Finset.sum_subtype (fourWickInternalPositions π).powerset
        (fun s => Finset.mem_powerset) (fun s => (-1 : ℂ) ^ s.card)).symm

/-- The actual four-normal-block moment has the finite inclusion-exclusion expansion.
The proof expands seven-term polynomials, uses only ordinary monomial Wick, and groups by full matchings. -/
theorem complexGaussian_four_normal_blocks_inclusion_exclusion_sum
    {I : Type*} [Fintype I] [DecidableEq I] (i j : FourWickPosition → I) :
    complexGaussianPolyExpectation
      (∏ b : Fin 4, gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1))) =
      fourWickInclusionExclusionSum i j := by
  classical
  rw [fourNormalQuartics_completion_expansion]
  have hw q := fourWick_completion_sum q
    (fun π => ∏ a, if i a = j (π a) then (1 : ℂ) else 0)
  simp_rw [hw]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold fourWickInclusionExclusionSum
  apply Finset.sum_congr rfl
  intro π _
  rw [← fourWick_expansion_coefficient_via_fiber, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp

/-- Finite normal-order expansion gives the permutation sum without internal contractions. -/
theorem complexGaussian_four_normal_blocks_finite_inclusion_exclusion
    {I : Type*} [Fintype I] [DecidableEq I] (i j : FourWickPosition → I) :
    complexGaussianPolyExpectation
      (∏ b : Fin 4, gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1))) =
      ∑ π ∈ fourBlockDerangements, ∏ a, if i a = j (π a) then (1 : ℂ) else 0 := by
  rw [complexGaussian_four_normal_blocks_inclusion_exclusion_sum,
    fourWickInclusionExclusionSum_eq]

end CertificationGaussian
