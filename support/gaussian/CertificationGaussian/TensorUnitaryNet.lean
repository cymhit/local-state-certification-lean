import CertificationGaussian.UnitaryNet
import Mathlib.LinearAlgebra.UnitaryGroup

noncomputable section
open scoped BigOperators
open Classical
namespace CertificationGaussian

/-- The actual product-basis matrix on the unique qudit index used by the quartic model. -/
def tensorUnitaryMatrix (d n : Nat) (U : Fin n → LocalUnitary d) :
    Matrix (QuditIndex d n) (QuditIndex d n) ℂ := fun x y => ∏ i, (U i).1 (x i) (y i)

theorem tensorUnitaryMatrix_unitary (d n : Nat) (U : Fin n → LocalUnitary d) :
    tensorUnitaryMatrix d n U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    tensorUnitaryMatrix, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (κ := fun _ : Fin n => Fin d)
    (fun i j => star ((U i).1 j (x i)) * (U i).1 j (y i))]
  have h (i : Fin n) : (∑ j, star ((U i).1 j (x i)) * (U i).1 j (y i)) =
      (1 : Matrix (Fin d) (Fin d) ℂ) (x i) (y i) := by
    have hi := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A (x i) (y i)) (U i).2.1
    exact hi
  simp_rw [h, Matrix.one_apply]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one, ← funext_iff]

/-- A coarse product perturbation bound: each factor has norm at most one. -/
theorem norm_prod_sub_prod_le {α : Type*} (s : Finset α) (u v : α → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 1) (hv : ∀ i ∈ s, ‖v i‖ ≤ 1)
    (hclose : ∀ i ∈ s, ‖u i-v i‖ ≤ ε) :
    ‖(∏ i ∈ s, u i) - ∏ i ∈ s, v i‖ ≤ s.card * ε := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have huS : ∀ i ∈ s, ‖u i‖ ≤ 1 := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hvS : ∀ i ∈ s, ‖v i‖ ≤ 1 := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hcS : ∀ i ∈ s, ‖u i-v i‖ ≤ ε := fun i hi => hclose i (Finset.mem_insert_of_mem hi)
    have hp : ‖∏ i ∈ s, u i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) huS
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have he : u a * (∏ i ∈ s, u i) - v a * (∏ i ∈ s, v i) =
        (u a-v a)*(∏ i ∈ s, u i) + v a*((∏ i ∈ s, u i)-(∏ i ∈ s, v i)) := by ring
    rw [he]
    calc
      _ ≤ ‖(u a-v a)*(∏ i ∈ s, u i)‖ + ‖v a*((∏ i ∈ s, u i)-(∏ i ∈ s, v i))‖ := norm_add_le _ _
      _ = ‖u a-v a‖ * ‖∏ i ∈ s, u i‖ + ‖v a‖ * ‖(∏ i ∈ s, u i)-(∏ i ∈ s, v i)‖ := by rw [norm_mul, norm_mul]
      _ ≤ ε*1 + 1*(s.card*ε) := by
        exact add_le_add (mul_le_mul (hclose a (Finset.mem_insert_self _ _)) hp (norm_nonneg _) hε)
          (mul_le_mul (hv a (Finset.mem_insert_self _ _)) (ih huS hvS hcS) (norm_nonneg _) (by norm_num))
      _ = _ := by rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]; ring

/-- Coordinatewise local matrix closeness implies entrywise product-basis closeness. -/
theorem tensorUnitaryMatrix_entry_close {d n : Nat} (U V : Fin n → LocalUnitary d)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ k i j, ‖(U k).1 i j-(V k).1 i j‖ ≤ ε)
    (x y : QuditIndex d n) :
    ‖tensorUnitaryMatrix d n U x y-tensorUnitaryMatrix d n V x y‖ ≤ n*ε := by
  simpa only [tensorUnitaryMatrix, Finset.card_univ, Fintype.card_fin] using
    norm_prod_sub_prod_le Finset.univ (fun k => (U k).1 (x k) (y k))
      (fun k => (V k).1 (x k) (y k)) hε
      (fun k _ => entry_norm_bound_of_unitary (U k).2 _ _)
      (fun k _ => entry_norm_bound_of_unitary (V k).2 _ _) (fun k _ => hclose k _ _)

/-- A deliberately coarse n*D*epsilon Euclidean bound suffices for the same final cubic rate. -/
theorem tensorUnitaryMatrix_operator_close {d n : Nat} (U V : Fin n → LocalUnitary d)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ k i j, ‖(U k).1 i j-(V k).1 i j‖ ≤ ε) :
    ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ)
      (tensorUnitaryMatrix d n U-tensorUnitaryMatrix d n V)‖ ≤ n*(d:ℝ)^n*ε := by
  apply (matrix_operator_norm_le_entry_sqrt _).trans
  have hs : (∑ x, ∑ y, ‖tensorUnitaryMatrix d n U x y-tensorUnitaryMatrix d n V x y‖^2) ≤
      ((n:ℝ)*(d:ℝ)^n*ε)^2 := by
    calc
      _ ≤ ∑ _x : QuditIndex d n, ∑ _y : QuditIndex d n, ((n:ℝ)*ε)^2 := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact pow_le_pow_left₀ (norm_nonneg _) (tensorUnitaryMatrix_entry_close U V hε hclose x y) 2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, qudit_card, nsmul_eq_mul, Nat.cast_pow]; ring
  exact (Real.sqrt_le_sqrt hs).trans_eq (Real.sqrt_sq (by positivity))

/-- The local squared-error bound controls each actual matrix entry. -/
theorem unitaryNet_covers_entry {d : Nat} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (U : LocalUnitary d) :
    ∃ V ∈ unitaryNet d hd ε hε, ∀ i j, ‖U.1 i j-V.1 i j‖ ≤ ε := by
  obtain ⟨V, hV, he⟩ := unitaryNet_covers_sq hd hε U
  refine ⟨V, hV, ?_⟩
  intro i j
  apply (sq_le_sq₀ (norm_nonneg _) hε.le).mp
  apply le_trans ?_ he
  exact (Finset.single_le_sum (f := fun j => ‖U.1 i j-V.1 i j‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖U.1 i j-V.1 i j‖^2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i))

def productUnitaryTupleNet (d n : Nat) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    Finset (Fin n → LocalUnitary d) :=
  Fintype.piFinset (fun _ => unitaryNet d hd ε hε)

/-- The finite family contains only actual tensor products of actual local unitaries. -/
def productUnitaryMatrixNet (d n : Nat) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :=
  (productUnitaryTupleNet d n hd ε hε).image (tensorUnitaryMatrix d n)

theorem productUnitaryMatrixNet_unitary {d n : Nat} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {W : Matrix (QuditIndex d n) (QuditIndex d n) ℂ}
    (hW : W ∈ productUnitaryMatrixNet d n hd ε hε) :
    W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) := by
  obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hW
  exact tensorUnitaryMatrix_unitary d n V

theorem productUnitaryMatrixNet_covers {d n : Nat} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (U : Fin n → LocalUnitary d) :
    ∃ W ∈ productUnitaryMatrixNet d n hd ε hε,
      ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ)
        (tensorUnitaryMatrix d n U-W)‖ ≤ n*(d:ℝ)^n*ε := by
  choose V hm hc using fun k => unitaryNet_covers_entry hd hε (U k)
  refine ⟨tensorUnitaryMatrix d n V, Finset.mem_image.mpr ⟨V, ?_, rfl⟩, ?_⟩
  · exact Fintype.mem_piFinset.mpr hm
  · exact tensorUnitaryMatrix_operator_close U V hε.le hc

theorem productUnitaryMatrixNet_card {d n : Nat} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ((productUnitaryMatrixNet d n hd ε hε).card:ℝ) ≤ (2+4*d/ε)^(2*d^2*n) := by
  have h1 : (productUnitaryMatrixNet d n hd ε hε).card ≤ (unitaryNet d hd ε hε).card^n := by
    apply (Finset.card_image_le).trans
    simp only [productUnitaryTupleNet, Fintype.card_piFinset_const, le_refl]
  have h1R : ((productUnitaryMatrixNet d n hd ε hε).card:ℝ) ≤ ((unitaryNet d hd ε hε).card^n:Nat) :=
    Nat.cast_le.mpr h1
  rw [Nat.cast_pow] at h1R
  apply h1R.trans
  simpa only [pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) (unitaryNet_card hd hε) n

end CertificationGaussian
