import LocalCertification.Extremal.OrderedDual
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
open scoped BigOperators Topology
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

def barycentricDenominator {n : ℕ} (x : Fin (n+1) → ℝ) (i : Fin (n+1)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (x i-x j)

theorem barycentricDenominator_formula {n : ℕ} (x : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    barycentricDenominator x i =
      (∏ j ∈ Finset.Iio i, (x i-x j)) *
        ((-1 : ℝ)^(n-(i : ℕ)) * ∏ j ∈ Finset.Ioi i, (x j-x i)) := by
  classical
  have he : Finset.univ.erase i = Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
      Finset.mem_Iio, Finset.mem_Ioi]
    omega
  have hd : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have h1 := Finset.mem_Iio.mp hj
    have h2 := Finset.mem_Ioi.mp hk
    omega
  unfold barycentricDenominator
  rw [he, Finset.prod_union hd]
  congr 1
  calc
    (∏ j ∈ Finset.Ioi i, (x i-x j)) = ∏ j ∈ Finset.Ioi i, -(x j-x i) := by
      apply Finset.prod_congr rfl
      intro j _
      ring
    _ = _ := by rw [Finset.prod_neg, Fin.card_Ioi]; simp

theorem barycentric_signed_pos {n : ℕ} (x : Fin (n+1) → ℝ) (hx : StrictMono x)
    (i : Fin (n+1)) : 0 < (-1 : ℝ)^(n-(i : ℕ)) * barycentricDenominator x i := by
  have hl : 0 < ∏ j ∈ Finset.Iio i, (x i-x j) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr (hx (Finset.mem_Iio.mp hj)))
  have hr : 0 < ∏ j ∈ Finset.Ioi i, (x j-x i) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr (hx (Finset.mem_Ioi.mp hj)))
  have hs : (-1 : ℝ)^(n-(i : ℕ)) * (-1 : ℝ)^(n-(i : ℕ)) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [barycentricDenominator_formula]
  calc
    0 < (∏ j ∈ Finset.Iio i, (x i-x j)) * (∏ j ∈ Finset.Ioi i, (x j-x i)) := mul_pos hl hr
    _ = ((-1 : ℝ)^(n-(i : ℕ)) * (-1 : ℝ)^(n-(i : ℕ))) *
        ((∏ j ∈ Finset.Iio i, (x i-x j)) * (∏ j ∈ Finset.Ioi i, (x j-x i))) := by rw [hs, one_mul]
    _ = _ := by ring

theorem barycentric_ratio_pos {n : ℕ} (x : Fin (n+1) → ℝ) (hx : StrictMono x)
    (i : Fin (n+1)) : 0 < (-1 : ℝ)^(n-(i : ℕ)) / barycentricDenominator x i :=
  div_pos_iff.mpr (mul_pos_iff.mp (barycentric_signed_pos x hx i))

theorem barycentric_sum_eq_zero {n : ℕ} (x : Fin (n+1) → ℝ) (hx : StrictMono x)
    (p : ℝ[X]) (hp : p.natDegree < n) :
    ∑ i, p.eval (x i) / barycentricDenominator x i = 0 := by
  have hd : p.degree < ((Finset.univ : Finset (Fin (n+1))).card : WithBot ℕ) := by
    apply lt_of_le_of_lt p.degree_le_natDegree
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_lt]
    omega
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := x) hx.injective.injOn hd
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    Polynomial.coeff_eq_zero_of_natDegree_lt hp, barycentricDenominator] using h.symm

/-- Alternating values with a bounded common offset require the full polynomial degree. -/
theorem alternating_offset_degree_lower (n : ℕ) (hn : 1 ≤ n)
    (x : Fin (n+1) → ℝ) (hx : StrictMono x) (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 < a i)
    (h : ℝ) (hh : |h| ≤ 1) (p : ℝ[X])
    (he : ∀ i, p.eval (x i) = a i * ((-1 : ℝ)^(i : ℕ)-h)) : n ≤ p.natDegree := by
  by_contra hp
  have hp' : p.natDegree < n := lt_of_not_ge hp
  have hid (i : Fin (n+1)) : (-1 : ℝ)^n * (p.eval (x i)/barycentricDenominator x i) =
      a i * ((-1 : ℝ)^(n-(i : ℕ))/barycentricDenominator x i) * (1-(-1 : ℝ)^(i : ℕ)*h) := by
    have hi : (i : ℕ) ≤ n := by omega
    have hs : (-1 : ℝ)^(i : ℕ)*(-1 : ℝ)^(i : ℕ) = 1 := by rw [← mul_pow]; norm_num
    have hsplit : (-1 : ℝ)^n = (-1 : ℝ)^(n-(i : ℕ)) * (-1 : ℝ)^(i : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    rw [he i, hsplit]
    calc
      _ = a i * ((-1 : ℝ)^(n-(i : ℕ))/barycentricDenominator x i) *
          ((-1 : ℝ)^(i : ℕ) * ((-1 : ℝ)^(i : ℕ)-h)) := by ring
      _ = _ := by rw [mul_sub, hs]
  have hf (i : Fin (n+1)) : 0 ≤ 1-(-1 : ℝ)^(i : ℕ)*h := by
    have ha' : |(-1 : ℝ)^(i : ℕ)*h| ≤ 1 := by simpa using hh
    have hl := (le_abs_self ((-1 : ℝ)^(i : ℕ)*h)).trans ha'
    linarith
  have hex : ∃ i : Fin (n+1), 0 < 1-(-1 : ℝ)^(i : ℕ)*h := by
    by_cases hl : h < 1
    · refine ⟨0, ?_⟩
      simpa using sub_pos.mpr hl
    · refine ⟨⟨1, by omega⟩, ?_⟩
      have heq : h = 1 := le_antisymm (abs_le.mp hh).2 (le_of_not_gt hl)
      simp [heq]
  have hsum : 0 < ∑ i, (-1 : ℝ)^n * (p.eval (x i)/barycentricDenominator x i) := by
    apply Finset.sum_pos'
    · intro i _
      rw [hid i]
      exact mul_nonneg (mul_pos (ha i) (barycentric_ratio_pos x hx i)).le (hf i)
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_univ i, by rw [hid i]; exact mul_pos (mul_pos (ha i) (barycentric_ratio_pos x hx i)) hi⟩
  rw [← Finset.mul_sum, barycentric_sum_eq_zero x hx p hp', mul_zero] at hsum
  exact lt_irrefl 0 hsum

end LocalCertification.Extremal
