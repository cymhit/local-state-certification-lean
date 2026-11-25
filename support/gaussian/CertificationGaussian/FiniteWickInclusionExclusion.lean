import CertificationGaussian.ComplexGaussianFourBlockWick
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Set

noncomputable section
open Finset MvPolynomial
open scoped BigOperators
namespace CertificationGaussian

/-- A contraction is an edge between labelled bar and ordinary positions. -/
abbrev FourWickPosition := Fin 4 × Fin 2

/-- Internal edges of a fixed complete matching, indexed by their bar positions.
This index never identifies positions whose coordinate values happen to coincide. -/
def fourWickInternalPositions (π : Equiv.Perm FourWickPosition) : Finset FourWickPosition :=
  univ.filter (fun a => (π a).1 = a.1)

/-- The exact finite alternating-subset identity used in normal ordering. -/
theorem finiteWick_subset_cancellation {A : Type*} [DecidableEq A] (s : Finset A) :
    (∑ t ∈ s.powerset, (-1 : ℂ) ^ t.card) = if s = ∅ then 1 else 0 := by
  have h := Finset.sum_powerset_neg_one_pow_card (x := s)
  exact_mod_cast h

/-- No internal edge is precisely the original four-block derangement condition. -/
theorem fourWickInternalPositions_empty_iff (π : Equiv.Perm FourWickPosition) :
    fourWickInternalPositions π = ∅ ↔ π ∈ fourBlockDerangements := by
  simp [fourWickInternalPositions, fourBlockDerangements, Finset.filter_eq_empty_iff]

/-- Each complete matching has coefficient zero or one after finite normal-order cancellation. -/
theorem fourWick_matching_coefficient (π : Equiv.Perm FourWickPosition) :
    (∑ s ∈ (fourWickInternalPositions π).powerset, (-1 : ℂ) ^ s.card) =
      if π ∈ fourBlockDerangements then 1 else 0 := by
  simp only [finiteWick_subset_cancellation, fourWickInternalPositions_empty_iff]

/-- The signed, complete-matching expansion before any cancellation. -/
def fourWickInclusionExclusionSum {I : Type*} [DecidableEq I]
    (i j : FourWickPosition → I) : ℂ :=
  ∑ π : Equiv.Perm FourWickPosition,
    (∑ s ∈ (fourWickInternalPositions π).powerset, (-1 : ℂ) ^ s.card) *
      ∏ a, if i a = j (π a) then 1 else 0

/-- Finite inclusion-exclusion leaves exactly the original no-internal permutation sum. -/
theorem fourWickInclusionExclusionSum_eq {I : Type*} [DecidableEq I]
    (i j : FourWickPosition → I) :
    fourWickInclusionExclusionSum i j =
      ∑ π ∈ fourBlockDerangements, ∏ a, if i a = j (π a) then (1 : ℂ) else 0 := by
  unfold fourWickInclusionExclusionSum
  simp_rw [fourWick_matching_coefficient]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp

end CertificationGaussian
