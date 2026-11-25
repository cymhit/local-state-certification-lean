import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
namespace CertificationGaussian
variable {S K : Type*} [Fintype S] [DecidableEq S] [DecidableEq K]

/-- The original support of a product label, relative to the distinguished identity label. -/
def radialBellSupport (k0 : K) (w : S → K) : Finset S :=
  Finset.univ.filter (fun s => w s≠k0)

/-- Local A0 eigenvalues, before tensorization. -/
def radialBellAWeight (d : ℕ) (k0 k : K) : ℝ := if k=k0 then 1 else (d+1:ℝ)⁻¹

/-- Local R0 eigenvalues, before tensorization. -/
def radialBellRWeight (d : ℕ) (k0 k : K) : ℝ := if k=k0 then 0 else (d+1:ℝ)⁻¹

/-- The first actual radial sequence q^(-w) sum_j d^j lambda_j choose(w,j). -/
def radialFirstCoefficient (d r : ℕ) (lam : ℕ → ℝ) (w : ℕ) : ℝ :=
  ((d+1:ℝ)⁻¹)^w * ∑ j : Fin (r+1),(d:ℝ)^j.val*lam j.val*(w.choose j.val:ℝ)

/-- The second original sequence, with squared coefficients and its factor two. -/
def radialSecondCoefficient (d r : ℕ) (lam : ℕ → ℝ) (w : ℕ) : ℝ :=
  2*radialFirstCoefficient d r (fun j => (lam j)^2) w

/-- A complementary site must be in the actual nonidentity support; every supported site contributes q^-1. -/
theorem radialBell_product_weights (d : ℕ) (k0 : K) (w : S → K) (J : Finset S) :
    (∏ s,if s∈J then radialBellRWeight d k0 (w s) else radialBellAWeight d k0 (w s)) =
      if J⊆radialBellSupport k0 w then ((d+1:ℝ)⁻¹)^(radialBellSupport k0 w).card else 0 := by
  by_cases hJ : J⊆radialBellSupport k0 w
  · rw [ite_eq_left hJ]
    calc
      _ = ∏ s : S,if s∈radialBellSupport k0 w then (d+1:ℝ)⁻¹ else 1 := by
        apply Finset.prod_congr rfl
        intro s _
        have hmem : s∈radialBellSupport k0 w ↔ w s≠k0 := by simp [radialBellSupport]
        by_cases hs : s∈J
        · have hw := hmem.mp (hJ hs)
          simp [hs,hmem,hw,radialBellRWeight]
        · by_cases hw : w s=k0 <;> simp [hs,hmem,hw,radialBellAWeight]
      _ = _ := by rw [Finset.prod_ite_mem_eq]; simp
  · rw [ite_eq_right hJ]
    obtain ⟨s,hs,hnot⟩ := Finset.not_subset.mp hJ
    have hw : w s=k0 := by simpa [radialBellSupport] using hnot
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs,radialBellRWeight,hw])

/-- Cardinality-j subsets contained in a fixed support have exactly choose(weight,j) multiplicity. -/
theorem radialBell_subset_count (T : Finset S) (j : ℕ) :
    (∑ J : {A : Finset S // A.card=j},if J.val⊆T then (1:ℝ) else 0)=
      (T.card.choose j:ℝ) := by
  let e : {J : {A : Finset S // A.card=j} // J.val⊆T} ≃
      {A : Finset S // A∈T.powersetCard j} :=
    { toFun := fun J => ⟨J.val.val,Finset.mem_powersetCard.mpr ⟨J.property,J.val.property⟩⟩
      invFun := fun A => ⟨⟨A.val,(Finset.mem_powersetCard.mp A.property).2⟩,
        (Finset.mem_powersetCard.mp A.property).1⟩
      left_inv := by intro J; rfl
      right_inv := by intro A; rfl }
  have hc : Fintype.card {J : {A : Finset S // A.card=j} // J.val⊆T}=T.card.choose j := by
    rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard]
  rw [← hc,Fintype.card_subtype]
  simp only [Finset.sum_boole]

/-- Summing the genuine site products over all subsets produces the exact original radial coefficient. -/
theorem radialBell_weight_formula (d r : ℕ) (lam : ℕ → ℝ) (k0 : K) (w : S → K) :
    (∑ j : Fin (r+1),(d:ℝ)^j.val*lam j.val*
      ∑ J : {A : Finset S // A.card=j.val},
        ∏ s,if s∈J.val then radialBellRWeight d k0 (w s) else radialBellAWeight d k0 (w s)) =
      radialFirstCoefficient d r lam (radialBellSupport k0 w).card := by
  simp only [radialBell_product_weights,radialFirstCoefficient]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ J : {A : Finset S // A.card=j.val},
        if J.val⊆radialBellSupport k0 w then ((d+1:ℝ)⁻¹)^(radialBellSupport k0 w).card else 0) =
      ((radialBellSupport k0 w).card.choose j.val:ℝ)*((d+1:ℝ)⁻¹)^(radialBellSupport k0 w).card := by
    rw [← radialBell_subset_count (radialBellSupport k0 w) j.val,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J _
    split_ifs <;> simp
  rw [he]
  ring

end CertificationGaussian
