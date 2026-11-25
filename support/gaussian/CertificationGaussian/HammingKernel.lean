import CertificationGaussian.Model
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/- Exact-distance counting and signed Hamming kernel identities.
The count is valid for arbitrary finite dimensions. Stochastic identities
explicitly require d >= 2 and k <= n, so no zero denominator is hidden. -/
noncomputable section
open scoped BigOperators
open Finset
namespace CertificationGaussian

/-- Coordinates at which two words differ. -/
def differenceSupport {d n : Nat} (x y : QuditIndex d n) : Finset (Fin n) :=
  univ.filter (fun i => x i ≠ y i)

@[simp] theorem card_differenceSupport {d n : Nat} (x y : QuditIndex d n) :
    (differenceSupport x y).card = hammingDistance x y := rfl

theorem hammingDistance_eq_hammingDist {d n : Nat} (x y : QuditIndex d n) :
    hammingDistance x y = hammingDist x y := rfl

@[simp] theorem hammingDistance_self {d n : Nat} (x : QuditIndex d n) :
    hammingDistance x x = 0 := hammingDist_self x

theorem hammingDistance_comm {d n : Nat} (x y : QuditIndex d n) :
    hammingDistance x y = hammingDistance y x := hammingDist_comm x y

private def differenceFiberEquiv {d n : Nat} (x : QuditIndex d n) (s : Finset (Fin n)) :
    {y : QuditIndex d n // differenceSupport x y = s} ≃
      (∀ i : Fin n, {a : Fin d // x i ≠ a ↔ i ∈ s}) :=
  (Equiv.subtypeEquivRight (fun y => by
    simp only [Finset.ext_iff, differenceSupport, Finset.mem_filter, Finset.mem_univ,
      true_and])).trans Equiv.subtypePiEquivPi

/-- A specified set of changed coordinates has exactly (d-1)^|s| choices. -/
theorem card_differenceFiber {d n : Nat} (x : QuditIndex d n) (s : Finset (Fin n)) :
    Fintype.card {y : QuditIndex d n // differenceSupport x y = s} = (d-1)^s.card := by
  classical
  rw [Fintype.card_congr (differenceFiberEquiv x s), Fintype.card_pi]
  have hcard (i : Fin n) : Fintype.card {a : Fin d // x i ≠ a ↔ i ∈ s} =
      if i ∈ s then d-1 else 1 := by
    by_cases hi : i ∈ s <;> simp [hi, Fintype.card_subtype_compl]
  simp_rw [hcard]
  simp

/-- Exact Hamming spheres have binomial(n,k)*(d-1)^k elements, including all edge cases. -/
theorem hamming_sphere_card {d n : Nat} (x : QuditIndex d n) (k : Nat) :
    (univ.filter (fun y : QuditIndex d n => hammingDistance x y = k)).card =
      Nat.choose n k * (d-1)^k := by
  classical
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (differenceSupport x)
    (p := fun y => hammingDistance x y = k) (q := fun s => s.card = k)
    (fun y => Iff.rfl)
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {y : QuditIndex d n // hammingDistance x y = k} =
        ∑ s : {s : Finset (Fin n) // s.card = k},
          Fintype.card {y : QuditIndex d n // differenceSupport x y = s.val} := by
      rw [← Fintype.card_congr e, Fintype.card_sigma]
    _ = ∑ _s : {s : Finset (Fin n) // s.card = k}, (d-1)^k := by
      apply Finset.sum_congr rfl
      intro s _
      rw [card_differenceFiber, s.property]
    _ = Nat.choose n k * (d-1)^k := by simp

/-- Positive sphere denominators in the physical dimension and legal shell range. -/
theorem distance_denominator_pos {d n k : Nat} (hd : 2 ≤ d) (hk : k ≤ n) :
    0 < (Nat.choose n k : ℝ) * ((d-1 : Nat) : ℝ)^k := by
  have hc : 0 < Nat.choose n k := Nat.choose_pos hk
  have hd' : 0 < d-1 := by omega
  exact mul_pos (Nat.cast_pos.mpr hc) (pow_pos (Nat.cast_pos.mpr hd') k)

theorem distanceAverage_nonneg (d n k : Nat) (x y : QuditIndex d n) :
    0 ≤ distanceAverage d n k x y := by
  unfold distanceAverage
  split_ifs <;> positivity

theorem distanceAverage_symm (d n k : Nat) (x y : QuditIndex d n) :
    distanceAverage d n k x y = distanceAverage d n k y x := by
  simp only [distanceAverage, hammingDistance_comm x y]

theorem distanceAverage_row_sum {d n k : Nat} (hd : 2 ≤ d) (hk : k ≤ n)
    (x : QuditIndex d n) : ∑ y, distanceAverage d n k x y = 1 := by
  classical
  simp only [distanceAverage, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, hamming_sphere_card]
  push_cast
  exact mul_inv_cancel₀ (ne_of_gt (distance_denominator_pos hd hk))

theorem distanceAverage_column_sum {d n k : Nat} (hd : 2 ≤ d) (hk : k ≤ n)
    (y : QuditIndex d n) : ∑ x, distanceAverage d n k x y = 1 := by
  simp_rw [distanceAverage_symm d n k _ y]
  exact distanceAverage_row_sum hd hk y

theorem signedHammingKernel_symm (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (x y : QuditIndex d n) :
    signedHammingKernel d n J θ x y = signedHammingKernel d n J θ y x := by
  simp only [signedHammingKernel, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [distanceAverage_symm]

theorem signedHammingKernel_row_sum {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (x : QuditIndex d n) :
    ∑ y, signedHammingKernel d n J θ x y = ∑ k ∈ J, θ k := by
  classical
  simp only [signedHammingKernel, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.mul_sum, distanceAverage_row_sum hd (hJ k hk), mul_one]

theorem signedHammingKernel_preserves_constants {d n : Nat} (hd : 2 ≤ d)
    (J : Finset Nat) (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (hθ : ∑ k ∈ J, θ k = 1) :
    (signedHammingKernel d n J θ).mulVec (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, mul_one, signedHammingKernel_row_sum hd J hJ θ, hθ]


/-- Distinct exact-distance rows have disjoint entry supports. -/
theorem distanceAverage_row_inner {d n k : Nat} (hd : 2 ≤ d) (hk : k ≤ n)
    (l : Nat) (x : QuditIndex d n) :
    ∑ y, distanceAverage d n k x y * distanceAverage d n l x y =
      if k = l then ((Nat.choose n k : ℝ) * ((d-1 : Nat) : ℝ)^k)⁻¹ else 0 := by
  classical
  by_cases hkl : k = l
  · subst l
    simp only [ite_true]
    have he (y : QuditIndex d n) :
        distanceAverage d n k x y * distanceAverage d n k x y =
          ((Nat.choose n k : ℝ) * ((d-1 : Nat) : ℝ)^k)⁻¹ * distanceAverage d n k x y := by
      unfold distanceAverage
      split_ifs <;> ring
    simp_rw [he]
    rw [← Finset.mul_sum, distanceAverage_row_sum hd hk, mul_one]
  · simp only [hkl, ite_false]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : hammingDistance x y = k
    · simp [distanceAverage, hy, hkl]
    · simp [distanceAverage, hy]

theorem signedHammingKernel_apply (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (x y : QuditIndex d n) :
    signedHammingKernel d n J θ x y = ∑ k ∈ J, θ k * distanceAverage d n k x y := by
  simp only [signedHammingKernel, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- Every row has squared Euclidean length v_n, for arbitrary real signed coefficients. -/
theorem signedHammingKernel_row_sq {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (x : QuditIndex d n) :
    ∑ y, (signedHammingKernel d n J θ x y)^2 = kernelVarianceScale d n J θ := by
  classical
  simp only [pow_two, signedHammingKernel_apply]
  calc
    ∑ y, (∑ k ∈ J, θ k * distanceAverage d n k x y) *
        (∑ l ∈ J, θ l * distanceAverage d n l x y) =
        ∑ k ∈ J, ∑ l ∈ J, θ k * θ l *
          (∑ y, distanceAverage d n k x y * distanceAverage d n l x y) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = kernelVarianceScale d n J θ := by
      unfold kernelVarianceScale
      apply Finset.sum_congr rfl
      intro k hk
      simp_rw [distanceAverage_row_inner hd (hJ k hk)]
      simp [hk, pow_two, div_eq_mul_inv]

/-- The diagonal of R_n squared is exactly the defined variance scale. -/
theorem signedHammingKernel_sq_diag {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (x : QuditIndex d n) :
    (signedHammingKernel d n J θ * signedHammingKernel d n J θ) x x =
      kernelVarianceScale d n J θ := by
  rw [Matrix.mul_apply]
  calc
    ∑ y, signedHammingKernel d n J θ x y * signedHammingKernel d n J θ y x =
        ∑ y, (signedHammingKernel d n J θ x y)^2 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [signedHammingKernel_symm d n J θ y x, pow_two]
    _ = _ := signedHammingKernel_row_sq hd J hJ θ x

/-- The real trace identity, with D = d^n. -/
theorem signedHammingKernel_sq_trace {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) :
    Matrix.trace (signedHammingKernel d n J θ * signedHammingKernel d n J θ) =
      (d^n : Nat) * kernelVarianceScale d n J θ := by
  simp only [Matrix.trace, Matrix.diag, signedHammingKernel_sq_diag hd J hJ θ,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, qudit_card]

theorem kernelVarianceScale_nonneg (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ) :
    0 ≤ kernelVarianceScale d n J θ := by
  unfold kernelVarianceScale
  apply Finset.sum_nonneg
  intro k _
  positivity


/-- The variance scale is the normalized trace of the square of the signed Hamming kernel. -/
theorem kernelVarianceScale_eq_trace_div {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) :
    kernelVarianceScale d n J θ =
      Matrix.trace (signedHammingKernel d n J θ * signedHammingKernel d n J θ) / (d^n : Nat) := by
  have hd0 : d ≠ 0 := by omega
  have hD : ((d^n : Nat) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero n hd0)
  rw [signedHammingKernel_sq_trace hd J hJ θ]
  field_simp

end CertificationGaussian
