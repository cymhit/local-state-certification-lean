import LocalCertification.Extremal.Extremizer
import LocalCertification.Extremal.CompactConvexHull
import Mathlib.Analysis.LocallyConvex.Separation

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Set Finset
noncomputable section
namespace LocalCertification.Extremal

/-- The compact signed dictionary uses all positive nodes and infinity. -/
def signedDictionary (q : ℝ) (r : ℕ) : Set (CoeffSpace r) :=
  Set.range (evaluationDictionary q r) ∪ Set.range (fun x => -evaluationDictionary q r x)

theorem signedDictionary_compact (q : ℝ) (hq : 1 < q) (r : ℕ) :
    IsCompact (signedDictionary q r) :=
  (isCompact_range (evaluationDictionary_continuous q hq r)).union
    (isCompact_range (evaluationDictionary_continuous q hq r).neg)

theorem signedDictionary_pos (q : ℝ) (r : ℕ) (x : OnePoint ℕ) :
    evaluationDictionary q r x ∈ signedDictionary q r := Or.inl ⟨x, rfl⟩

theorem signedDictionary_neg (q : ℝ) (r : ℕ) (x : OnePoint ℕ) :
    -evaluationDictionary q r x ∈ signedDictionary q r := Or.inr ⟨x, rfl⟩

def dualCoefficients {r : ℕ} (f : CoeffSpace r →ₗ[ℝ] ℝ) : CoeffSpace r :=
  (f (1, 0), fun j => f (0, Pi.single j 1))

theorem pairing_dualCoefficients {r : ℕ} (f : CoeffSpace r →ₗ[ℝ] ℝ) (v : CoeffSpace r) :
    pairing (dualCoefficients f) v = f v := by
  have hv : v = v.1 • (1, 0) + ∑ j : Fin (r+1), v.2 j • (0, Pi.single j 1) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · funext i
      simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  calc
    pairing (dualCoefficients f) v = f (v.1 • (1, 0) + ∑ j : Fin (r+1), v.2 j • (0, Pi.single j 1)) := by
      simp only [map_add, map_sum, map_smul, smul_eq_mul]
      simp [pairing, dualCoefficients, mul_comm]
    _ = f v := congrArg f hv.symm

theorem pairing_smul_left {r : ℕ} (a : ℝ) (c v : CoeffSpace r) :
    pairing (a • c) v = a * pairing c v := by
  rw [pairing_comm, map_smul, smul_eq_mul, pairing_comm c v]

def normalizedExtrapolation (q : ℝ) (r : ℕ) : CoeffSpace r :=
  (extremalValue q r)⁻¹ • extrapolationDictionary r

/-- Finite-dimensional separation places the actual extrapolation vector in the signed hull. -/
theorem normalizedExtrapolation_mem_signedHull (q : ℝ) (hq : 1 < q) (r : ℕ) :
    normalizedExtrapolation q r ∈ convexHull ℝ (signedDictionary q r) := by
  by_contra hn
  obtain ⟨f, u, hf, hy⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (compact_convexHull (signedDictionary_compact q hq r)).isClosed hn
  have hp (x : OnePoint ℕ) := hf _ (subset_convexHull ℝ _ (signedDictionary_pos q r x))
  have hm (x : OnePoint ℕ) := hf _ (subset_convexHull ℝ _ (signedDictionary_neg q r x))
  have hu : 0 < u := by
    have h₁ := hp ∞
    have h₂ := hm ∞
    rw [map_neg] at h₂
    linarith
  let c : CoeffSpace r := u⁻¹ • dualCoefficients f.toLinearMap
  have hc : c ∈ feasible q r := by
    intro x
    rw [← pairing_dictionary]
    change |pairing (u⁻¹ • dualCoefficients f.toLinearMap) (evaluationDictionary q r x)| ≤ 1
    rw [pairing_smul_left, pairing_dualCoefficients, abs_mul, abs_of_pos (inv_pos.mpr hu)]
    have hab : |f (evaluationDictionary q r x)| ≤ u := by
      rw [abs_le]
      have h₁ := hp x
      have h₂ := hm x
      rw [map_neg] at h₂
      constructor <;> linarith
    calc
      _ ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hu.le)
      _ = 1 := inv_mul_cancel₀ hu.ne'
  have hbound := extrapolation_le_extremalValue q hq r hc
  have hv : 0 < extremalValue q r := lt_trans zero_lt_one (one_lt_extremalValue q hq r)
  rw [normalizedExtrapolation, map_smul, smul_eq_mul] at hy
  have he : extrapolation r c = u⁻¹ * f (extrapolationDictionary r) := by
    rw [extrapolation, pairing_comm]
    exact (pairing_smul_left _ _ _).trans (congrArg (fun t => u⁻¹*t)
      (pairing_dualCoefficients f.toLinearMap _))
  rw [he] at hbound
  have hlarge : u * extremalValue q r < f (extrapolationDictionary r) := by
    calc
      _ < (extremalValue q r)⁻¹ * f (extrapolationDictionary r) * extremalValue q r :=
        mul_lt_mul_of_pos_right hy hv
      _ = _ := by field_simp
  have hsmall : f (extrapolationDictionary r) ≤ u * extremalValue q r := by
    have h := mul_le_mul_of_nonneg_left hbound hu.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul] using h
  exact (not_lt_of_ge hsmall) hlarge

theorem feasible_signed_le_one (q : ℝ) (r : ℕ) {c z : CoeffSpace r}
    (hc : c ∈ feasible q r) (hz : z ∈ signedDictionary q r) : pairing c z ≤ 1 := by
  rcases hz with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [pairing_dictionary]
    exact (abs_le.mp (hc x)).2
  · rw [map_neg, pairing_dictionary]
    exact neg_le.mpr (abs_le.mp (hc x)).1

/-- Every maximizer exposes a genuine contact-hull representation of the extrapolation vector. -/
theorem normalizedExtrapolation_mem_contactHull (q : ℝ) (hq : 1 < q) (r : ℕ)
    {c : CoeffSpace r} (hc : c ∈ feasible q r) (hmax : extrapolation r c = extremalValue q r) :
    normalizedExtrapolation q r ∈ convexHull ℝ (contactDictionary q r c) := by
  obtain ⟨ι, hι, z, a, hz, ha, hpos, hsum, he⟩ := eq_pos_convex_span_of_mem_convexHull
    (normalizedExtrapolation_mem_signedHull q hq r)
  have hv : extremalValue q r ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_extremalValue q hq r))
  have hone : pairing c (normalizedExtrapolation q r) = 1 := by
    rw [normalizedExtrapolation, map_smul, smul_eq_mul, pairing_comm]
    change (extremalValue q r)⁻¹ * extrapolation r c = 1
    rw [hmax, inv_mul_cancel₀ hv]
  have hweighted : ∑ i, a i * pairing c (z i) = 1 := by
    have h := congrArg (pairing c) he
    simpa only [map_sum, map_smul, smul_eq_mul, hone] using h
  have hnonneg (i : ι) : 0 ≤ a i * (1 - pairing c (z i)) :=
    mul_nonneg (hpos i).le (sub_nonneg.mpr (feasible_signed_le_one q r hc (hz ⟨i, rfl⟩)))
  have hzero : ∑ i, a i * (1 - pairing c (z i)) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum, hweighted, sub_self]
  have hcontact (i : ι) : pairing c (z i) = 1 := by
    have ht : a i * (1 - pairing c (z i)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero i (Finset.mem_univ i)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left (ne_of_gt (hpos i)))).symm
  apply mem_convexHull_of_exists_fintype a z (fun i => (hpos i).le) hsum ?_ he
  intro i
  rcases hz ⟨i, rfl⟩ with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact ⟨x, 1, Or.inl rfl, by simpa using hx.symm, hcontact i⟩
  · exact ⟨x, -1, Or.inr rfl, by simpa using hx.symm, hcontact i⟩

end LocalCertification.Extremal
