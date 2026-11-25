import LocalCertification.Extremal.BinomialMoments

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- One actual extremal dual certificate, retaining every degree-bounded polynomial identity
alongside its masses, positive integer nodes, and alternating nonzero coefficients. -/
structure IntegerDualCertificate (q : ℝ) (r : ℕ) where
  node : Fin (r+1) → ℕ
  weight : Fin (r+1) → ℝ
  infinityWeight : ℝ
  node_strictMono : StrictMono node
  node_pos : ∀ i, 0 < node i
  weight_ne_zero : ∀ i, weight i ≠ 0
  infinityWeight_ne_zero : infinityWeight ≠ 0
  mass : (∑ i, weight i) + infinityWeight = 1
  variation : (∑ i, |weight i|) + |infinityWeight| = extremalValue q r
  weight_sign : ∀ i : Fin (r+1), 0 < (-1 : ℝ)^(i : ℕ) * weight i
  infinityWeight_sign : 0 < (-1 : ℝ)^(r+1) * infinityWeight
  reproduce : ∀ p : ℝ[X], p.natDegree ≤ r →
    ∑ i, weight i * q^(-(node i : ℝ)) * p.eval (node i : ℝ) = p.eval 0

/-- All certificate fields come from the same complete dual, not from separate choices. -/
theorem integerDualCertificate_nonempty (q : ℝ) (hq : 1 < q) (r : ℕ) :
    Nonempty (IntegerDualCertificate q r) := by
  obtain ⟨c, x, a, hc, hm, hx, ho, hinf, ha, he, hv, hs, _, _, _⟩ := finite_extremal_dual_complete q hq r
  obtain ⟨j, hj, heq⟩ := ordered_finite_labels r x hx ho hinf
  refine ⟨{ node := fun i => j i+1
            weight := fun i => a i.castSucc
            infinityWeight := a (Fin.last (r+1))
            node_strictMono := ?_
            node_pos := fun _ => Nat.zero_lt_succ _
            weight_ne_zero := fun i => ha i.castSucc
            infinityWeight_ne_zero := ha _
            mass := ?_
            variation := ?_
            weight_sign := fun i => hs i.castSucc
            infinityWeight_sign := hs (Fin.last (r+1))
            reproduce := ?_ }⟩
  · intro i k hik
    exact Nat.add_lt_add_right (hj hik) 1
  · have h := finite_dual_mass q r x a he
    rwa [Fin.sum_univ_castSucc] at h
  · rwa [Fin.sum_univ_castSucc] at hv
  · intro p hp
    have h := finite_dual_polynomial q r x a he p hp
    rw [Fin.sum_univ_castSucc] at h
    simp only [hinf, polynomialNode_infty, mul_zero, add_zero] at h
    simpa only [← heq, polynomialNode_real_formula, zero_add, mul_assoc] using h.symm

/-- A fixed choice depending only on q and r, independent of system size and target. -/
def extremalIntegerDual (q : ℝ) (hq : 1 < q) (r : ℕ) : IntegerDualCertificate q r :=
  Classical.choice (integerDualCertificate_nonempty q hq r)

/-- The finite binomial moments belong to this very same polynomial-reproducing certificate. -/
theorem IntegerDualCertificate.binomial_moments {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r)
    (k : ℕ) (hk : k ≤ r) :
    ∑ i, c.weight i * q^(-(c.node i : ℝ)) * ((c.node i).choose k : ℝ) =
      if k=0 then 1 else 0 := by
  simpa only [binomialPolynomial_eval_nat, binomialPolynomial_eval_zero] using
    c.reproduce (binomialPolynomial k) ((binomialPolynomial_degree k).trans hk)

end LocalCertification.Extremal
