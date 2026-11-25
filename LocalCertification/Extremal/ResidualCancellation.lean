import LocalCertification.Extremal.ResidualMass

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace LocalCertification.Extremal

/-- Zero binomial tails permit a common finite summation range for every actual node. -/
theorem binomial_weighted_sum_extended (d j M : ℕ) (hj : j ≤ M) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (j+1), (j.choose k : ℝ)*(d : ℝ)^k*f k) =
      ∑ k ∈ Finset.range (M+1), (j.choose k : ℝ)*(d : ℝ)^k*f k := by
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hj 1))
  intro k _ hk
  simp only [Finset.mem_range, not_lt] at hk
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]

/-- All low radii cancel against the target for this actual dual certificate. -/
theorem residual_cancellation (d : ℕ) {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r)
    (f : ℕ → ℝ) :
    f 0 - ∑ i, c.weight i*q^(-(c.node i : ℝ)) *
      (∑ k ∈ Finset.range (c.node i+1), ((c.node i).choose k : ℝ)*(d : ℝ)^k*f k) =
      ∑ k ∈ residualRadii c, residualCoefficient d c k * f k := by
  classical
  let T := Finset.range (c.maxNode+1)
  have hall : (∑ k ∈ T, residualCoefficient d c k * f k) =
      -∑ i, c.weight i*q^(-(c.node i : ℝ)) *
        (∑ k ∈ Finset.range (c.node i+1), ((c.node i).choose k : ℝ)*(d : ℝ)^k*f k) := by
    simp_rw [binomial_weighted_sum_extended d _ c.maxNode (c.node_le_maxNode _) f]
    simp only [T, residualCoefficient, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun k => k ≤ r)
    (fun k => residualCoefficient d c k*f k)
  have hlow : (∑ k ∈ T.filter (fun k => k ≤ r), residualCoefficient d c k*f k) = -f 0 := by
    rw [Finset.sum_eq_single 0]
    · rw [residualCoefficient_low d c (Nat.zero_le r)]
      simp
    · intro k hk hk0
      rw [residualCoefficient_low d c (Finset.mem_filter.mp hk).2, ite_eq_right hk0, zero_mul]
    · intro h
      exact False.elim (h (by simp [T]))
  have hhigh : T.filter (fun k => ¬ k ≤ r) = residualRadii c := by
    ext k
    simp only [T, Finset.mem_filter, Finset.mem_range, residualRadii, Finset.mem_Icc]
    omega
  rw [hlow, hhigh, hall] at hsplit
  linarith

/-- The same cancellation using the normalized, possibly signed, residual weights. -/
theorem residual_cancellation_normalized (d : ℕ) {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) (f : ℕ → ℝ) :
    f 0 - ∑ i, c.weight i*q^(-(c.node i : ℝ)) *
      (∑ k ∈ Finset.range (c.node i+1), ((c.node i).choose k : ℝ)*(d : ℝ)^k*f k) =
      c.infinityWeight * ∑ k ∈ residualRadii c, residualWeight d c k * f k := by
  rw [residual_cancellation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold residualWeight
  field_simp [c.infinityWeight_ne_zero]

end LocalCertification.Extremal
