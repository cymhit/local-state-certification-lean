import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open Matrix Finset Unitary
open scoped BigOperators
namespace CertificationGaussian

/-- Weighted arithmetic-geometric mean at complementary integer powers. -/
theorem complementary_powers_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {k l : Nat} (hk : 0 < k) (hl : l ≤ k) :
    a^l*b^(k-l) ≤ ((l:ℝ)/k)*a^k + ((k-l:Nat):ℝ)/k*b^k := by
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hk)
  have hw : (l:ℝ)/k + ((k-l:Nat):ℝ)/k = 1 := by
    rw [← add_div, Nat.cast_sub hl]
    field_simp
    ring
  have h := Real.geom_mean_le_arith_mean2_weighted
    (p₁ := a^k) (p₂ := b^k) (w₁ := (l:ℝ)/k) (w₂ := ((k-l:Nat):ℝ)/k)
    (by positivity) (by positivity) (pow_nonneg ha _) (pow_nonneg hb _) hw
  have he (c : ℝ) (hc : 0 ≤ c) (r : Nat) :
      (c^k)^((r:ℝ)/k) = c^r := by
    rw [← Real.rpow_natCast c k, ← Real.rpow_mul hc]
    rw [mul_div_cancel₀ _ hk', Real.rpow_natCast]
  simpa only [he a ha l, he b hb (k-l)] using h

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The Hermitian sandwich trace in a real diagonal eigenbasis is a real weighted double sum. -/
theorem hermitian_diagonal_sandwich_trace (H : Matrix N N ℂ) (hH : H.IsHermitian)
    (ev : N → ℝ) (l m : Nat) :
    Matrix.trace (H*(Matrix.diagonal (fun i => (ev i : ℂ)))^l*
      H*(Matrix.diagonal (fun i => (ev i : ℂ)))^m) =
      (∑ a, ∑ b, ‖H a b‖^2 * (ev b)^l * (ev a)^m : ℝ) := by
  simp only [Matrix.diagonal_pow, Matrix.trace, Matrix.diag_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
  simp only [Matrix.mul_diagonal, Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [← hH.apply b a]
  rw [Complex.sq_norm]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self,
    starRingEnd_apply]
  ring

/-- The diagonal version of the noncommutative trace sandwich estimate, including empty matrices. -/
theorem hermitian_diagonal_sandwich_bound (H : Matrix N N ℂ) (hH : H.IsHermitian)
    (ev : N → ℝ) {k l : Nat} (hk : 0 < k) (heven : Even k) (hl : l ≤ k) :
    ‖Matrix.trace (H*(Matrix.diagonal (fun i => (ev i : ℂ)))^l*
      H*(Matrix.diagonal (fun i => (ev i : ℂ)))^(k-l))‖ ≤
      (Matrix.trace (H^2*(Matrix.diagonal (fun i => (ev i : ℂ)))^k)).re := by
  have hr : Matrix.trace (H^2*(Matrix.diagonal (fun i => (ev i : ℂ)))^k) =
      ((∑ a, ∑ b, ‖H a b‖^2 * (ev a)^k : ℝ) : ℂ) := by
    simpa [pow_two] using hermitian_diagonal_sandwich_trace H hH ev 0 k
  rw [hermitian_diagonal_sandwich_trace H hH, hr, Complex.ofReal_re, Complex.norm_real,
    Real.norm_eq_abs]
  have hsym (a b : N) : ‖H a b‖^2 = ‖H b a‖^2 := by
    rw [← hH.apply a b, norm_star]
  have heq : (∑ a, ∑ b, ‖H a b‖^2*|ev b|^k) =
      ∑ a, ∑ b, ‖H a b‖^2*|ev a|^k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hsym b a]
  calc
    |∑ a, ∑ b, ‖H a b‖^2*(ev b)^l*(ev a)^(k-l)|
      ≤ ∑ a, ∑ b, ‖H a b‖^2*|ev b|^l*|ev a|^(k-l) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro a _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro b _
        simp [abs_mul, abs_pow, abs_of_nonneg (sq_nonneg ‖H a b‖)]
    _ ≤ ∑ a, ∑ b, ‖H a b‖^2 *
        (((l:ℝ)/k)*|ev b|^k + ((k-l:Nat):ℝ)/k*|ev a|^k) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (complementary_powers_le _ _ (abs_nonneg _) (abs_nonneg _) hk hl) (sq_nonneg _)
    _ = ((l:ℝ)/k)*(∑ a, ∑ b, ‖H a b‖^2*|ev b|^k) +
        ((k-l:Nat):ℝ)/k*(∑ a, ∑ b, ‖H a b‖^2*|ev a|^k) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
    _ = ∑ a, ∑ b, ‖H a b‖^2*(ev a)^k := by
        rw [heq, ← add_mul, ← add_div, Nat.cast_sub hl]
        have hcoef : ((l:ℝ)+((k:ℝ)-l))/k = 1 := by
          field_simp
          ring
        rw [hcoef, one_mul]
        simp only [heven.pow_abs]

/-- Trace is unchanged by actual unitary conjugation, with no nonempty-dimension assumption. -/
theorem trace_unitary_conjugation (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    Matrix.trace (conjStarAlgAut ℂ (Matrix N N ℂ) U A) = Matrix.trace A := by
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- The noncommutative sandwich estimate for arbitrary Hermitian matrices at positive even order. -/
theorem hermitian_trace_sandwich_pos (H X : Matrix N N ℂ) (hH : H.IsHermitian)
    (hX : X.IsHermitian) {k l : Nat} (hk : 0 < k) (heven : Even k) (hl : l ≤ k) :
    ‖Matrix.trace (H*X^l*H*X^(k-l))‖ ≤ (Matrix.trace (H^2*X^k)).re := by
  let e := conjStarAlgAut ℂ (Matrix N N ℂ) (star hX.eigenvectorUnitary)
  have hX' : e X = Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) :=
    hX.conjStarAlgAut_star_eigenvectorUnitary
  have hH' : (e H).IsHermitian := by
    change star (e H) = e H
    rw [← map_star]
    exact congrArg e hH
  have h := hermitian_diagonal_sandwich_bound (e H) hH' hX.eigenvalues hk heven hl
  have hleft : e (H*X^l*H*X^(k-l)) = e H*(Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)))^l*
      e H*(Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)))^(k-l) := by
    simp only [map_mul, map_pow, hX']
  have hright : e (H^2*X^k) = (e H)^2*(Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)))^k := by
    simp only [map_mul, map_pow, hX']
  rw [← hleft, ← hright] at h
  simpa only [e, trace_unitary_conjugation] using h

/-- The zeroth-order sandwich, needed separately when the trace moment has order two. -/
theorem hermitian_trace_square_norm (H : Matrix N N ℂ) (hH : H.IsHermitian) :
    ‖Matrix.trace (H^2)‖ = (Matrix.trace (H^2)).re := by
  have h := hermitian_diagonal_sandwich_trace H hH (fun _ => 0) 0 0
  simp only [pow_zero, mul_one, ← pow_two] at h
  rw [h, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  apply abs_of_nonneg
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))

/-- Full even-order Hermitian trace sandwich, including k=0 and empty matrix indices. -/
theorem hermitian_trace_sandwich (H X : Matrix N N ℂ) (hH : H.IsHermitian)
    (hX : X.IsHermitian) {k l : Nat} (heven : Even k) (hl : l ≤ k) :
    ‖Matrix.trace (H*X^l*H*X^(k-l))‖ ≤ (Matrix.trace (H^2*X^k)).re := by
  by_cases hk : k = 0
  · subst k
    have hl0 : l = 0 := Nat.eq_zero_of_le_zero hl
    subst l
    simp only [pow_zero, mul_one, Nat.sub_self, ← pow_two]
    exact (hermitian_trace_square_norm H hH).le
  · exact hermitian_trace_sandwich_pos H X hH hX (Nat.pos_of_ne_zero hk) heven hl

end CertificationGaussian
