import CertificationGaussian.ComplexGaussianBlockWick
import CertificationGaussian.ComplexGaussianNormalMatrix

noncomputable section
open MeasureTheory MvPolynomial Finset
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Positions are two separate slots in each of four blocks. -/
def fourBlockPositionEquiv : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv

omit [Fintype I] in
theorem gaussianNormalQuartic_creation_form (a b c d : I) :
    gaussianNormalQuartic a b c d =
      gaussianBarCreation a (gaussianBarCreation b (gaussianZPolynomial c*gaussianZPolynomial d)) := by
  have h1 (k : I) : wirtingerBar k (1 : MvPolynomial (Fin 2 × I) ℂ)=0 := by
    simpa only [map_one] using wirtingerBar_C k 1
  simp only [gaussianNormalQuartic,gaussianZCreation,h1,mul_one,sub_zero,wirtingerBar_z]

omit [Fintype I] in
/-- The general colored polynomial really is the seven-term quartic in every one of the four blocks. -/
theorem gaussianNormalBlock_four (i j : Fin 4 × Fin 2 → I) (b : Fin 4) :
    gaussianNormalBlock 8 8
      (fun a => (fourBlockPositionEquiv.symm a).1) (fun a => (fourBlockPositionEquiv.symm a).1)
      (fun a => i (fourBlockPositionEquiv.symm a)) (fun a => j (fourBlockPositionEquiv.symm a)) b =
      gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1)) := by
  rw [gaussianNormalQuartic_creation_form]
  fin_cases b <;>
    norm_num [gaussianNormalBlock,Fin.prod_univ_succ,fourBlockPositionEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat]

/-- Every edge must leave its entire block, not merely its own position. -/
def fourBlockDerangements : Finset (Equiv.Perm (Fin 4 × Fin 2)) :=
  Finset.univ.filter (fun π => ∀ a, (π a).1 ≠ a.1)

omit [Fintype I] in
theorem complexGaussianBlockPairingSum_four (i j : Fin 4 × Fin 2 → I) :
    complexGaussianBlockPairingSum 8
      (fun a => (fourBlockPositionEquiv.symm a).1) (fun a => (fourBlockPositionEquiv.symm a).1)
      (fun a => i (fourBlockPositionEquiv.symm a)) (fun a => j (fourBlockPositionEquiv.symm a)) =
      ∑ π ∈ fourBlockDerangements, ∏ a, if i a=j (π a) then (1:ℂ) else 0 := by
  unfold complexGaussianBlockPairingSum
  rw [← fourBlockPositionEquiv.permCongr.sum_comp
    (fun π : Equiv.Perm (Fin 8) => ∏ a,
      if (fourBlockPositionEquiv.symm a).1 ≠ (fourBlockPositionEquiv.symm (π a)).1 ∧
        i (fourBlockPositionEquiv.symm a)=j (fourBlockPositionEquiv.symm (π a)) then (1:ℂ) else 0)]
  simp only [fourBlockDerangements,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro π _
  rw [← fourBlockPositionEquiv.prod_comp
    (fun a : Fin 8 => if (fourBlockPositionEquiv.symm a).1 ≠
      (fourBlockPositionEquiv.symm (fourBlockPositionEquiv.permCongr π a)).1 ∧
      i (fourBlockPositionEquiv.symm a)=j (fourBlockPositionEquiv.symm (fourBlockPositionEquiv.permCongr π a))
      then (1:ℂ) else 0)]
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  by_cases hp : ∀ a, (π a).1 ≠ a.1
  · rw [ite_eq_left hp]
    apply Finset.prod_congr rfl
    intro a _
    simp [Ne.symm (hp a)]
  · rw [ite_eq_right hp]
    push Not at hp
    obtain ⟨a,ha⟩ := hp
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [ha]

/-- The four-block Wick identity before matrix-entry contraction. -/
theorem complexGaussian_four_normal_blocks (i j : Fin 4 × Fin 2 → I) :
    complexGaussianPolyExpectation
      (∏ b : Fin 4, gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1))) =
      ∑ π ∈ fourBlockDerangements, ∏ a, if i a=j (π a) then (1:ℂ) else 0 := by
  have h := complexGaussian_block_wick 8
    (fun a => (fourBlockPositionEquiv.symm a).1) (fun a => (fourBlockPositionEquiv.symm a).1)
    (fun a => i (fourBlockPositionEquiv.symm a)) (fun a => j (fourBlockPositionEquiv.symm a))
  simpa only [gaussianNormalProduct,gaussianNormalBlock_four,complexGaussianBlockPairingSum_four] using h

/-- All labels coincident give the exact admissible permutation count, certified by the true scalar moment. -/
theorem fourBlockDerangements_card : fourBlockDerangements.card = 4752 := by
  have h := complexGaussian_four_normal_blocks (I := Fin 1) (fun _ => 0) (fun _ => 0)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  rw [gaussianNormalQuartic_same_fourth] at h
  simp only [ite_true,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at h
  exact_mod_cast h.symm

end CertificationGaussian
