import CertificationGaussian.FiniteWickInclusionExclusionFourBlock

noncomputable section
open Finset MvPolynomial
open scoped BigOperators
namespace CertificationGaussian

/-- The finite expansion route independently recovers the exact 4752 admissible position matchings. -/
theorem fourBlockDerangements_card_finite_inclusion_exclusion :
    fourBlockDerangements.card = 4752 := by
  have h := complexGaussian_four_normal_blocks_finite_inclusion_exclusion
    (I := Fin 1) (fun _ => 0) (fun _ => 0)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [gaussianNormalQuartic_same_fourth] at h
  simp only [ite_true, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm

/-- The paper's 8! upper bound counts labelled positions, including all coincidences. -/
theorem fourBlockDerangements_card_le_eight_factorial :
    fourBlockDerangements.card ≤ Nat.factorial 8 := by
  calc
    fourBlockDerangements.card ≤ Fintype.card (Equiv.Perm FourWickPosition) := Finset.card_le_univ _
    _ = Nat.factorial 8 := by simp [Fintype.card_perm, FourWickPosition]

/-- Every repeated-coordinate pattern is allowed: no injectivity hypothesis appears. -/
theorem complexGaussian_four_normal_blocks_repeated_labels
    (i j : FourWickPosition → Fin 2) :
    complexGaussianPolyExpectation
      (∏ b : Fin 4, gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1))) =
      ∑ π ∈ fourBlockDerangements, ∏ a, if i a = j (π a) then (1 : ℂ) else 0 :=
  complexGaussian_four_normal_blocks_finite_inclusion_exclusion i j

/-- At the maximally coincident boundary all 4752 admissible position matchings remain. -/
theorem complexGaussian_four_normal_blocks_all_equal
    {I : Type*} [Fintype I] [DecidableEq I] (k : I) :
    complexGaussianPolyExpectation (gaussianNormalQuartic k k k k ^ 4) = (4752 : ℂ) := by
  have h := complexGaussian_four_normal_blocks_finite_inclusion_exclusion
    (fun _ => k) (fun _ => k)
  simpa [fourBlockDerangements_card_finite_inclusion_exclusion] using h

/-- Uniform bound of each normal-block moment norm by the number of all eight-position permutations. -/
theorem complexGaussian_four_normal_blocks_finite_norm_le
    {I : Type*} [Fintype I] [DecidableEq I] (i j : FourWickPosition → I) :
    ‖complexGaussianPolyExpectation
      (∏ b : Fin 4, gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1)))‖ ≤
      (Nat.factorial 8 : ℝ) := by
  rw [complexGaussian_four_normal_blocks_finite_inclusion_exclusion]
  have ht (π : Equiv.Perm FourWickPosition) :
      ‖∏ a, if i a = j (π a) then (1 : ℂ) else 0‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro a _
      exact norm_nonneg _
    · intro a _
      split_ifs <;> simp
  calc
    _ ≤ ∑ π ∈ fourBlockDerangements, ‖∏ a, if i a = j (π a) then (1 : ℂ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _π ∈ fourBlockDerangements, (1 : ℝ) :=
      Finset.sum_le_sum (fun π _ => ht π)
    _ = (fourBlockDerangements.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (Nat.factorial 8 : ℝ) := by exact_mod_cast fourBlockDerangements_card_le_eight_factorial

end CertificationGaussian
