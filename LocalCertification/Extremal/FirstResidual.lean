import LocalCertification.Extremal.IntegerDual
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

set_option autoImplicit false
open scoped BigOperators
open Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- Subtracting the node root product removes the highest term of the binomial polynomial. -/
def firstResidualInterpolant {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) : ℝ[X] :=
  ((r+1).factorial : ℝ)⁻¹ •
    (descPochhammer ℝ (r+1) - ∏ i, (X - C (c.node i : ℝ)))

theorem firstResidualInterpolant_degree {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) :
    (firstResidualInterpolant c).natDegree ≤ r := by
  have hp : IsMonicOfDegree (descPochhammer ℝ (r+1)) (r+1) :=
    ⟨descPochhammer_natDegree ℝ _, monic_descPochhammer ℝ _⟩
  have hq : IsMonicOfDegree (∏ i, (X - C (c.node i : ℝ))) (r+1) := by
    refine ⟨?_, monic_prod_X_sub_C (fun i => (c.node i : ℝ)) Finset.univ⟩
    simpa using natDegree_finsetProd_X_sub_C_eq_card Finset.univ (fun i => (c.node i : ℝ))
  exact (Polynomial.natDegree_smul_le _ _).trans
    (Nat.le_of_lt_succ (IsMonicOfDegree.natDegree_sub_lt (by omega) hp hq))

theorem firstResidualInterpolant_at_node {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) (i : Fin (r+1)) :
    (firstResidualInterpolant c).eval (c.node i : ℝ) = ((c.node i).choose (r+1) : ℝ) := by
  have hz : (∏ k : Fin (r+1), (X - C (c.node k : ℝ))).eval (c.node i : ℝ) = 0 := by
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [firstResidualInterpolant, Polynomial.eval_smul, Polynomial.eval_sub, hz, sub_zero]
  simpa only [binomialPolynomial, Polynomial.eval_smul] using binomialPolynomial_eval_nat (r+1) (c.node i)

theorem firstResidualInterpolant_at_zero {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) :
    (firstResidualInterpolant c).eval 0 =
      -((r+1).factorial : ℝ)⁻¹ * ((-1 : ℝ)^(r+1) * ∏ i, (c.node i : ℝ)) := by
  simp [firstResidualInterpolant, Polynomial.eval_smul, Polynomial.eval_sub,
    Polynomial.eval_prod, Finset.prod_neg, mul_neg]

/-- The signed Hamming coefficient from the actual finite dual. -/
def residualCoefficient (d : ℕ) {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) (k : ℕ) : ℝ :=
  -(d : ℝ)^k * ∑ i, c.weight i * q^(-(c.node i : ℝ)) * ((c.node i).choose k : ℝ)

/-- Exact first residual coefficient, including r=0. No interpolation weights are assumed. -/
theorem first_residual_formula (d : ℕ) {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) :
    residualCoefficient d c (r+1) =
      (-1 : ℝ)^(r+1) * ((d : ℝ)^(r+1) / ((r+1).factorial : ℝ)) * ∏ i, (c.node i : ℝ) := by
  have h := c.reproduce (firstResidualInterpolant c) (firstResidualInterpolant_degree c)
  simp_rw [firstResidualInterpolant_at_node, firstResidualInterpolant_at_zero] at h
  rw [residualCoefficient, h]
  ring

/-- The first residual survives for every positive local dimension. -/
theorem first_residual_ne_zero {d : ℕ} (hd : 0 < d) {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) : residualCoefficient d c (r+1) ≠ 0 := by
  rw [first_residual_formula]
  apply mul_ne_zero
  · apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact div_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (c.node_pos i)))

/-- Normalizing by the actual nonzero infinity coefficient gives the signed residual kernel weights. -/
def residualWeight (d : ℕ) {q : ℝ} {r : ℕ} (c : IntegerDualCertificate q r) (k : ℕ) : ℝ :=
  residualCoefficient d c k / c.infinityWeight

/-- The leading residual weight is strictly positive by the proved dual alternation. -/
theorem first_residualWeight_pos {d : ℕ} (hd : 0 < d) {q : ℝ} {r : ℕ}
    (c : IntegerDualCertificate q r) : 0 < residualWeight d c (r+1) := by
  have hp : 0 < ((d : ℝ)^(r+1) / ((r+1).factorial : ℝ)) * ∏ i, (c.node i : ℝ) := by
    apply mul_pos
    · exact div_pos (pow_pos (Nat.cast_pos.mpr hd) _) (Nat.cast_pos.mpr (Nat.factorial_pos _))
    · exact Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (c.node_pos i))
  have hs : ((-1 : ℝ)^(r+1))^2 = 1 := by
    calc
      ((-1 : ℝ)^(r+1))^2 = ((-1 : ℝ)^2)^(r+1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = 1 := by norm_num
  have hcoef : 0 < (-1 : ℝ)^(r+1) * residualCoefficient d c (r+1) := by
    rw [first_residual_formula]
    nlinarith
  have h := div_pos hcoef c.infinityWeight_sign
  have hn : (-1 : ℝ)^(r+1) ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa only [mul_div_mul_left _ _ hn, residualWeight] using h

end LocalCertification.Extremal
