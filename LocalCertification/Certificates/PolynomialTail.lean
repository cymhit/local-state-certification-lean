import LocalCertification.Extremal.RationalExtremizer
import Mathlib.Algebra.Polynomial.Taylor

set_option autoImplicit false
open scoped BigOperators
open Polynomial
noncomputable section
namespace LocalCertification.Certificates

/-- A finite exact rational sign test, using the actual polynomial support. -/
def coefficientsNonnegative (p : ℚ[X]) : Prop :=
  ∀ k ∈ p.support, 0 ≤ p.coeff k

instance coefficientsNonnegative_decidable (p : ℚ[X]) : Decidable (coefficientsNonnegative p) :=
  inferInstanceAs (Decidable (∀ k ∈ p.support, 0 ≤ p.coeff k))

/-- The literal shifted coefficient array in the finite tail certificate. -/
def shiftedPolynomial (p : ℚ[X]) (M : ℕ) : ℚ[X] := p.comp (X + C (M : ℚ))

/-- The exact weighted-sequence difference, for every rational base q > 1. -/
def weightedDifference (q : ℚ) (p : ℚ[X]) : ℚ[X] := C q * p - p.comp (X + 1)

/-- Both arrays are finite, including constant or zero polynomials. -/
def tailCheck (q : ℚ) (p : ℚ[X]) (M : ℕ) : Prop :=
  coefficientsNonnegative (shiftedPolynomial p M) ∧
    coefficientsNonnegative (shiftedPolynomial (weightedDifference q p) M)

instance tailCheck_decidable (q : ℚ) (p : ℚ[X]) (M : ℕ) : Decidable (tailCheck q p M) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem coefficientsNonnegative_all {p : ℚ[X]} (hp : coefficientsNonnegative p) (k : ℕ) :
    0 ≤ p.coeff k := by
  by_cases hk : p.coeff k = 0
  · rw [hk]
  · exact hp k (Polynomial.mem_support_iff.mpr hk)

/-- Finite coefficient verification implies nonnegativity on the entire nonnegative rational ray. -/
theorem eval_nonneg_of_coefficients {p : ℚ[X]} (hp : coefficientsNonnegative p)
    {x : ℚ} (hx : 0 ≤ x) : 0 ≤ p.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (coefficientsNonnegative_all hp k) (pow_nonneg hx k))

theorem shifted_nonnegative_at {p : ℚ[X]} {M w : ℕ}
    (hp : coefficientsNonnegative (shiftedPolynomial p M)) (hw : M ≤ w) :
    0 ≤ p.eval (w : ℚ) := by
  have h := eval_nonneg_of_coefficients hp (Nat.cast_nonneg (w-M))
  have he : ((w-M : ℕ) : ℚ) + (M : ℚ) = (w : ℚ) := by
    exact_mod_cast Nat.sub_add_cancel hw
  simpa only [shiftedPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, he] using h

/-- This is the exact sequence whose monotonicity the two finite arrays certify. -/
def weightedPolynomial (q : ℚ) (p : ℚ[X]) (w : ℕ) : ℚ :=
  q⁻¹ ^ w * p.eval (w : ℚ)

theorem weightedPolynomial_step (q : ℚ) (hq : 0 < q) (p : ℚ[X]) (w : ℕ)
    (hR : 0 ≤ (weightedDifference q p).eval (w : ℚ)) :
    weightedPolynomial q p (w+1) ≤ weightedPolynomial q p w := by
  have h : p.eval ((w : ℚ)+1) ≤ q * p.eval (w : ℚ) := by
    simpa only [weightedDifference, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, sub_nonneg] using hR
  unfold weightedPolynomial
  push_cast
  calc
    q⁻¹ ^ (w+1) * p.eval ((w : ℚ)+1) ≤ q⁻¹ ^ (w+1) * (q * p.eval (w : ℚ)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.mpr hq.le) _)
    _ = q⁻¹ ^ w * p.eval (w : ℚ) := by
      rw [pow_succ]
      field_simp

/-- A finite tail check bounds every later integer, not just a sampled interval. -/
theorem tailCheck_bounds (q : ℚ) (hq : 0 < q) (p : ℚ[X]) (M : ℕ)
    (h : tailCheck q p M) (w : ℕ) (hw : M ≤ w) :
    0 ≤ weightedPolynomial q p w ∧ weightedPolynomial q p w ≤ weightedPolynomial q p M := by
  constructor
  · exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hq.le) w) (shifted_nonnegative_at h.1 hw)
  · have ha : Antitone (fun k : ℕ => weightedPolynomial q p (M+k)) := by
      apply antitone_nat_of_succ_le
      intro k
      simpa only [Nat.add_assoc] using weightedPolynomial_step q hq p (M+k)
        (shifted_nonnegative_at h.2 (Nat.le_add_right M k))
    have ht := ha (Nat.zero_le (w-M))
    simpa only [Nat.add_zero, Nat.add_sub_of_le hw] using ht

/-- The actual oriented extrapolation function: its infinity value is h with |h| = 1. -/
def orientedCandidateValue (q h : ℚ) (Q : ℚ[X]) (w : ℕ) : ℚ :=
  h * (1 - weightedPolynomial q Q w)

/-- A finite prefix and two finite shifted arrays imply every positive-integer constraint.
No limit, true feasibility, or desired infinite bound is included among the inputs. -/
theorem finite_prefix_tail_sound (q : ℚ) (hq : 0 < q) (h : ℚ) (hh : |h|=1)
    (Q : ℚ[X]) (M : ℕ) (hM : 1 ≤ M) (htail : tailCheck q Q M)
    (hprefix : ∀ w ∈ Finset.Icc 1 M, |orientedCandidateValue q h Q w| ≤ 1) :
    ∀ w : ℕ, 1 ≤ w → |orientedCandidateValue q h Q w| ≤ 1 := by
  intro w hw
  by_cases hwm : w ≤ M
  · exact hprefix w (Finset.mem_Icc.mpr ⟨hw,hwm⟩)
  · have hMval := hprefix M (Finset.mem_Icc.mpr ⟨hM,le_rfl⟩)
    have hb := tailCheck_bounds q hq Q M htail w (le_of_not_ge hwm)
    simp only [orientedCandidateValue, abs_mul, hh, one_mul] at hMval ⊢
    apply abs_le.mpr
    have hc := abs_le.mp hMval
    constructor <;> linarith

namespace Consumers
/-- Actual degree zero uses a nonzero constant: the finite tail test is already decisive at M = 1. -/
theorem positive_constant_tail : tailCheck 3 (1 : ℚ[X]) 1 := by
  constructor
  · intro k _
    by_cases hk : k = 0 <;> simp [shiftedPolynomial, Polynomial.coeff_one, hk]
  · intro k _
    by_cases hk : k = 0 <;> simp [shiftedPolynomial, weightedDifference, Polynomial.coeff_one, Polynomial.coeff_C, hk]

/-- A negative constant fails the exact finite array check; it cannot certify an infeasible tail. -/
theorem negative_constant_rejected : ¬ tailCheck 3 (-1 : ℚ[X]) 1 := by
  intro h
  have he := coefficientsNonnegative_all h.1 0
  norm_num [shiftedPolynomial] at he
end Consumers
end LocalCertification.Certificates
