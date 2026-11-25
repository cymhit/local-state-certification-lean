import LocalCertification.Certificates.Soundness

set_option autoImplicit false
open scoped BigOperators
open Polynomial
namespace LocalCertification.Certificates

/-- Executable rational coefficient arithmetic for p(M+X), with no Polynomial operation at runtime. -/
def shiftArrayCoeff (N : ℕ) (a : Fin N → ℚ) (M k : ℕ) : ℚ :=
  ∑ j : Fin N, a j * (j.val.choose k : ℚ) * (M : ℚ)^(j.val-k)

/-- This Boolean is computed entirely by finite sums, natural binomials and rational comparisons. -/
def arrayTailCheck (q : ℚ) (N : ℕ) (a : Fin N → ℚ) (M : ℕ) : Bool :=
  decide (∀ k : Fin N, 0 ≤ shiftArrayCoeff N a M k.val ∧
    0 ≤ q*shiftArrayCoeff N a M k.val-shiftArrayCoeff N a (M+1) k.val)

/-- The executable rational polynomial evaluator, including trailing zero coefficients. -/
def arrayEval (N : ℕ) (a : Fin N → ℚ) (x : ℚ) : ℚ := ∑ j : Fin N, a j*x^j.val

def arrayPrefixCheck (q h : ℚ) (N : ℕ) (a : Fin N → ℚ) (M : ℕ) : Bool :=
  decide (∀ w : Fin M, |h+q⁻¹^(w.val+1)*arrayEval N a ((w.val+1 : ℕ) : ℚ)|≤1)

/-- Exact correspondence between executable coefficients and the genuine shifted Polynomial. -/
theorem shiftArrayCoeff_eq (N : ℕ) (a : Fin N → ℚ) (M k : ℕ) :
    shiftArrayCoeff N a M k = (shiftedPolynomial (Polynomial.ofFn N a) M).coeff k := by
  rw [shiftedPolynomial, Polynomial.ofFn_eq_sum_monomial, Polynomial.sum_comp,
    Polynomial.finsetSum_coeff]
  unfold shiftArrayCoeff
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  ring

theorem shiftedDifference (q : ℚ) (p : ℚ[X]) (M : ℕ) :
    shiftedPolynomial (weightedDifference q p) M =
      C q * shiftedPolynomial p M-shiftedPolynomial p (M+1) := by
  simp only [shiftedPolynomial, weightedDifference, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.one_comp]
  congr 2
  push_cast
  simp only [map_add, map_one]
  ring

theorem shiftArrayCoeff_zero_of_ge (N : ℕ) (a : Fin N → ℚ) (M k : ℕ) (hk : N≤k) :
    shiftArrayCoeff N a M k = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : j.val<k := lt_of_lt_of_le j.isLt hk
  simp only [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, mul_zero, zero_mul]

/-- Successful executable finite checks certify the original infinite-tail mathematics. -/
theorem arrayTailCheck_sound (q : ℚ) (N : ℕ) (a : Fin N → ℚ) (M : ℕ)
    (h : arrayTailCheck q N a M = true) : tailCheck q (Polynomial.ofFn N a) M := by
  have ht : ∀ k : Fin N, 0 ≤ shiftArrayCoeff N a M k.val ∧
      0 ≤ q*shiftArrayCoeff N a M k.val-shiftArrayCoeff N a (M+1) k.val :=
    of_decide_eq_true h
  have hf (k : ℕ) : 0 ≤ shiftArrayCoeff N a M k ∧
      0 ≤ q*shiftArrayCoeff N a M k-shiftArrayCoeff N a (M+1) k := by
    by_cases hk : k<N
    · exact ht ⟨k,hk⟩
    · rw [shiftArrayCoeff_zero_of_ge N a M k (le_of_not_gt hk),
        shiftArrayCoeff_zero_of_ge N a (M+1) k (le_of_not_gt hk)]
      norm_num
  constructor
  · intro k _
    rw [← shiftArrayCoeff_eq]
    exact (hf k).1
  · intro k _
    rw [shiftedDifference, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      ← shiftArrayCoeff_eq, ← shiftArrayCoeff_eq]
    exact (hf k).2

/-- The executable test loses no mathematical tail certificate. -/
theorem arrayTailCheck_complete (q : ℚ) (N : ℕ) (a : Fin N → ℚ) (M : ℕ)
    (h : tailCheck q (Polynomial.ofFn N a) M) : arrayTailCheck q N a M = true := by
  apply decide_eq_true
  intro k
  constructor
  · rw [shiftArrayCoeff_eq]
    exact coefficientsNonnegative_all h.1 k.val
  · have hr := coefficientsNonnegative_all h.2 k.val
    rw [shiftedDifference, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      ← shiftArrayCoeff_eq, ← shiftArrayCoeff_eq] at hr
    exact hr

/-- A genuine positive leading coefficient guarantees the executable shift search finds a passing array. -/
theorem arrayTailCheck_exists (q : ℚ) (hq : 1 < q) (N : ℕ) (a : Fin N → ℚ)
    (hp : 0 < (Polynomial.ofFn N a).leadingCoeff) (J : ℕ) :
    ∃ k : ℕ, arrayTailCheck q N a (J+k) = true := by
  obtain ⟨M,hM,h⟩ := exists_tailCheck_after q hq (Polynomial.ofFn N a) hp J
  refine ⟨M-J,?_⟩
  rw [Nat.add_sub_of_le hM]
  exact arrayTailCheck_complete q N a M h

/-- Executable least-shift search. Its termination proof comes from the actual positive leading coefficient. -/
def findTailShift (q : ℚ) (hq : 1 < q) (N : ℕ) (a : Fin N → ℚ)
    (hp : 0 < (Polynomial.ofFn N a).leadingCoeff) (J : ℕ) : ℕ :=
  J + Nat.find (arrayTailCheck_exists q hq N a hp J)

theorem findTailShift_spec (q : ℚ) (hq : 1 < q) (N : ℕ) (a : Fin N → ℚ)
    (hp : 0 < (Polynomial.ofFn N a).leadingCoeff) (J : ℕ) :
    J ≤ findTailShift q hq N a hp J ∧
      arrayTailCheck q N a (findTailShift q hq N a hp J) = true :=
  ⟨Nat.le_add_right _ _, Nat.find_spec (arrayTailCheck_exists q hq N a hp J)⟩

theorem arrayEval_eq (N : ℕ) (a : Fin N → ℚ) (x : ℚ) :
    arrayEval N a x = (Polynomial.ofFn N a).eval x := by
  simp only [arrayEval, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

theorem arrayPrefixCheck_sound (q h : ℚ) (N : ℕ) (a : Fin N → ℚ) (M : ℕ)
    (he : arrayPrefixCheck q h N a M = true) :
    ∀ w ∈ Finset.Icc 1 M, |rationalCandidateValue q h (Polynomial.ofFn N a) w|≤1 := by
  have ht : ∀ w : Fin M, |h+q⁻¹^(w.val+1)*arrayEval N a ((w.val+1 : ℕ) : ℚ)|≤1 := of_decide_eq_true he
  intro w hw
  have hw' := Finset.mem_Icc.mp hw
  have hk : w-1<M := by omega
  have heq : w-1+1=w := by omega
  have hz := ht ⟨w-1,hk⟩
  simpa only [heq, arrayEval_eq, rationalCandidateValue, weightedPolynomial] using hz

namespace Consumers
/-- Kernel-checked arithmetic validates the actual executable constant tail test, without native_decide. -/
theorem constant_array_passes : arrayTailCheck 3 1 (fun _ => 6) 1 = true := by norm_num [arrayTailCheck, shiftArrayCoeff, arrayPrefixCheck, arrayEval, Fin.sum_univ_succ]

theorem negative_array_rejected : arrayTailCheck 3 1 (fun _ => -6) 1 = false := by norm_num [arrayTailCheck, shiftArrayCoeff, Fin.sum_univ_succ]

theorem constant_array_prefix : arrayPrefixCheck 3 (-1) 1 (fun _ => 6) 1 = true := by norm_num [arrayTailCheck, shiftArrayCoeff, arrayPrefixCheck, arrayEval, Fin.sum_univ_succ]
end Consumers
end LocalCertification.Certificates
