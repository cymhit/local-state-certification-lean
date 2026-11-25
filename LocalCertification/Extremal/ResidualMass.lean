import LocalCertification.Extremal.FirstResidual
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace LocalCertification.Extremal

/-- The largest physical shell label is fixed by the certificate, not by n or the target. -/
def IntegerDualCertificate.maxNode {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) : ℕ :=
  c.node (Fin.last r)

theorem IntegerDualCertificate.node_le_maxNode {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) (i : Fin (r+1)) : c.node i ≤ c.maxNode :=
  c.node_strictMono.monotone (Fin.le_last i)

theorem IntegerDualCertificate.degree_lt_maxNode {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) : r < c.maxNode := by
  classical
  have hsub : Finset.univ.image c.node ⊆ Finset.Icc 1 c.maxNode := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_Icc.mpr ⟨c.node_pos i, c.node_le_maxNode i⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ c.node_strictMono.injective] at h
  simpa using h

/-- The full binomial sum remains unchanged after extending beyond its integer degree. -/
theorem binomial_sum_extended (d j M : ℕ) (hj : j ≤ M) :
    (∑ k ∈ Finset.range (M+1), (j.choose k : ℝ) * (d : ℝ)^k) = ((d : ℝ)+1)^j := by
  calc
    _ = ∑ k ∈ Finset.range (j+1), (j.choose k : ℝ) * (d : ℝ)^k := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hj 1))
      intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    _ = _ := by simpa [mul_comm] using (add_pow (d : ℝ) 1 j).symm

/-- Low radii cancel, with the zeroth coefficient exactly -1 before adding the target. -/
theorem residualCoefficient_low (d : ℕ) {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) {k : ℕ} (hk : k ≤ r) :
    residualCoefficient d c k = if k=0 then -1 else 0 := by
  rw [residualCoefficient, c.binomial_moments k hk]
  by_cases h : k=0 <;> simp [h]

/-- At q=d+1 the entire finite Hamming expansion has the correct total mass. -/
theorem residualCoefficient_total (d : ℕ) (hd : 0 < d) {r : ℕ}
    (c : IntegerDualCertificate ((d : ℝ)+1) r) :
    (∑ k ∈ Finset.range (c.maxNode+1), residualCoefficient d c k) = -(∑ i, c.weight i) := by
  have hq : 0 < (d : ℝ)+1 := by positivity
  have he : (∑ k ∈ Finset.range (c.maxNode+1), residualCoefficient d c k) =
      -∑ i, c.weight i * ((d : ℝ)+1)^(-(c.node i : ℝ)) *
        (∑ k ∈ Finset.range (c.maxNode+1), ((c.node i).choose k : ℝ) * (d : ℝ)^k) := by
    simp only [residualCoefficient, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [binomial_sum_extended d (c.node i) c.maxNode (c.node_le_maxNode i)]
  rw [← Real.rpow_natCast, mul_assoc, ← Real.rpow_add hq]
  simp

/-- The finite support of the residual kernel consists only of radii above r. -/
def residualRadii {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) : Finset ℕ :=
  Finset.Icc (r+1) c.maxNode

/-- Its unnormalized signed mass is exactly the actual infinity atom. -/
theorem residualCoefficient_mass (d : ℕ) (hd : 0 < d) {r : ℕ}
    (c : IntegerDualCertificate ((d : ℝ)+1) r) :
    ∑ k ∈ residualRadii c, residualCoefficient d c k = c.infinityWeight := by
  classical
  let T := Finset.range (c.maxNode+1)
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun k => k ≤ r) (residualCoefficient d c)
  have hlow : ∑ k ∈ T.filter (fun k => k ≤ r), residualCoefficient d c k = -1 := by
    rw [Finset.sum_eq_single 0]
    · exact residualCoefficient_low d c (Nat.zero_le r)
    · intro k hk hk0
      rw [residualCoefficient_low d c (Finset.mem_filter.mp hk).2, ite_eq_right hk0]
    · intro h
      exact False.elim (h (by simp [T]))
  have hhigh : T.filter (fun k => ¬ k ≤ r) = residualRadii c := by
    ext k
    simp only [T, Finset.mem_filter, Finset.mem_range, residualRadii, Finset.mem_Icc]
    omega
  rw [hlow, hhigh, residualCoefficient_total d hd c] at hsplit
  linarith [c.mass]

/-- Normalized signed weights sum to one, with no positivity assumption on the other coefficients. -/
theorem residualWeight_mass (d : ℕ) (hd : 0 < d) {r : ℕ}
    (c : IntegerDualCertificate ((d : ℝ)+1) r) :
    ∑ k ∈ residualRadii c, residualWeight d c k = 1 := by
  simp only [residualWeight, div_eq_mul_inv, ← Finset.sum_mul]
  rw [residualCoefficient_mass d hd c, mul_inv_cancel₀ c.infinityWeight_ne_zero]

/-- The nonzero leading radius belongs to the actual fixed residual support. -/
theorem first_mem_residualRadii {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) :
    r+1 ∈ residualRadii c :=
  Finset.mem_Icc.mpr ⟨le_rfl, c.degree_lt_maxNode⟩

end LocalCertification.Extremal
