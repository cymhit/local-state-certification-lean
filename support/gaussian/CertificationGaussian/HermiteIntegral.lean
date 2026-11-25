/-
Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license; see licenses/GaussianField-LICENSE.
Extracted from gaussian-field dc2b3b8378b2b7e33eaa8b61d6e943de11ff3f33.
The proofs below are retained; general field/nuclear/lattice infrastructure is excluded.
The extraction selects the Hermite and Wick results needed by this Gaussian support library.
-/
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp

open MeasureTheory Polynomial Real
noncomputable section
private lemma integrable_pow_mul_exp_neg_mul_sq (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) volume := by
  have hcont : Continuous (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) := by fun_prop
  set C : ℝ := ↑k.factorial * Real.exp (1 / (2 * b))
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (half_pos hb)).const_mul C)
    hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  -- Goal: |x|^k * exp(-b*x²) ≤ C * exp(-(b/2)*x²)
  -- Step 1: |x|^k ≤ k! * exp(|x|) from Taylor bound
  have hpow : |x| ^ k ≤ ↑k.factorial * Real.exp (|x|) := by
    have hfact_pos : (0 : ℝ) < ↑k.factorial := Nat.cast_pos.mpr k.factorial_pos
    have h : |x| ^ k / ↑k.factorial ≤ Real.exp (|x|) := le_trans
      (Finset.single_le_sum
        (fun i (_ : i ∈ Finset.range (k + 1)) =>
          div_nonneg (pow_nonneg (abs_nonneg x) i) (Nat.cast_nonneg' (i.factorial)))
        (Finset.mem_range.mpr (by omega) : k ∈ Finset.range (k + 1)))
      (Real.sum_le_exp_of_nonneg (abs_nonneg x) (k + 1))
    rwa [div_le_iff₀ hfact_pos, mul_comm] at h
  -- Step 2: |x| ≤ (b/2)·x² + 1/(2b) by completing the square
  have hquad : |x| ≤ b / 2 * x ^ 2 + 1 / (2 * b) := by
    have heq : b / 2 * x ^ 2 + 1 / (2 * b) = (b ^ 2 * x ^ 2 + 1) / (2 * b) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
    nlinarith [sq_abs x, sq_nonneg (b * |x| - 1)]
  -- Step 3: Factor exp(-b·x²) = exp(-(b/2)·x²) · exp(-(b/2)·x²) and combine
  have hfactor : Real.exp (-b * x ^ 2) =
      Real.exp (-(b / 2) * x ^ 2) * Real.exp (-(b / 2) * x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hfactor, show |x| ^ k * (Real.exp (-(b / 2) * x ^ 2) * Real.exp (-(b / 2) * x ^ 2)) =
    (|x| ^ k * Real.exp (-(b / 2) * x ^ 2)) * Real.exp (-(b / 2) * x ^ 2) from by ring]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc |x| ^ k * Real.exp (-(b / 2) * x ^ 2)
      ≤ ↑k.factorial * Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ↑k.factorial * (Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2)) := by ring
    _ = ↑k.factorial * Real.exp (|x| + -(b / 2) * x ^ 2) := by
        rw [← Real.exp_add]
    _ ≤ ↑k.factorial * Real.exp (1 / (2 * b)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg' _)
        exact Real.exp_le_exp.mpr (by linarith)

/-- For any polynomial p and b > 0, the function x ↦ p(x) · exp(-b·x²) is integrable.
    Proved by polynomial induction, reducing to monomial integrability. -/
private lemma integrable_eval_mul_exp_neg_mul_sq (p : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) volume := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun x : ℝ => (p + q).eval x * Real.exp (-b * x ^ 2)) =
           (fun x => p.eval x * Real.exp (-b * x ^ 2)) +
           (fun x => q.eval x * Real.exp (-b * x ^ 2)) := by
      ext x; simp [Polynomial.eval_add, add_mul]
    rw [this]; exact hp.add hq
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    show Integrable (fun x : ℝ => a * x ^ k * Real.exp (-b * x ^ 2)) volume
    have heq : (fun x : ℝ => a * x ^ k * Real.exp (-b * x ^ 2)) =
               fun x => a * (x ^ k * Real.exp (-b * x ^ 2)) := by ext x; ring
    rw [heq]
    exact (integrable_pow_mul_exp_neg_mul_sq k hb).const_mul a

abbrev hermiteR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

/-- The derivative of the (n+1)-th Hermite polynomial is (n+1) times the n-th.
    Adapted from auto1's `probHermite_derivative`. -/
theorem hermite_derivative (n : ℕ) :
    derivative (hermite (n + 1)) = (↑(n + 1) : ℤ[X]) * hermite n := by
  induction n with
  | zero => simp [hermite_succ, hermite_zero]
  | succ n ih =>
    show derivative (X * hermite (n + 1) - derivative (hermite (n + 1)))
        = (↑(n + 2) : ℤ[X]) * hermite (n + 1)
    rw [map_sub, derivative_mul, derivative_X, one_mul]
    simp only [ih]
    rw [derivative_mul, derivative_natCast, zero_mul, zero_add]
    have step : hermite (n + 1) + X * ((↑(n + 1) : ℤ[X]) * hermite n) -
        (↑(n + 1) : ℤ[X]) * derivative (hermite n) =
        hermite (n + 1) +
        (↑(n + 1) : ℤ[X]) * (X * hermite n - derivative (hermite n)) := by ring
    rw [step, ← hermite_succ,
        show (↑(n + 2) : ℤ[X]) = 1 + ↑(n + 1) from by push_cast; ring]
    ring

/-- Derivative of Hermite polynomial over ℝ. -/
private theorem hermiteR_derivative (n : ℕ) :
    derivative (hermiteR (n + 1)) = (↑(n + 1) : ℝ[X]) * hermiteR n := by
  simp only [hermiteR]
  rw [Polynomial.derivative_map, hermite_derivative, Polynomial.map_mul, Polynomial.map_natCast]

/-- The unnormalized Gaussian weight `exp(-x²/2)` (no `1/√(2π)` factor). -/
abbrev gaussian (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

/-- Derivative of `Hₘ(x) · exp(-x²/2)` equals `-H_{m+1}(x) · exp(-x²/2)`.
    From `H_{m+1} = X·Hₘ - Hₘ'` and the product rule. -/
private theorem deriv_hermiteEval_mul_gaussian (m : ℕ) (x : ℝ) :
    deriv (fun u => (hermiteR m).eval u * gaussian u) x =
    -((hermiteR (m + 1)).eval x) * gaussian x := by
  have hdiff_exp : DifferentiableAt ℝ (fun u : ℝ => Real.exp (-(u ^ 2 / 2))) x :=
    DifferentiableAt.exp (by fun_prop)
  have hd := deriv_fun_mul (hermiteR m).differentiable.differentiableAt hdiff_exp
  rw [hd]
  -- Convert deriv of polynomial eval via aeval
  have hpoly : deriv (fun u => (hermiteR m).eval u) x = (derivative (hermiteR m)).eval x := by
    have h1 : (fun u => (hermiteR m).eval u) = fun u => Polynomial.aeval u (hermiteR m) := by
      ext u; simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
    rw [h1, Polynomial.deriv_aeval]
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
  rw [hpoly]
  have hexp : deriv (fun u : ℝ => Real.exp (-(u ^ 2 / 2))) x = -x * gaussian x := by
    have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      convert this using 1; ring
    exact h1.exp.deriv.trans (mul_comm _ _)
  rw [hexp]
  -- Hermite recurrence: H_{m+1}(x) = x · Hₘ(x) - Hₘ'(x)
  have hrec : (hermiteR (m + 1)).eval x = x * (hermiteR m).eval x - (derivative (hermiteR m)).eval x := by
    have h1 : hermiteR (m + 1) = X * hermiteR m - derivative (hermiteR m) := by
      unfold hermiteR
      rw [hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.derivative_map]
    rw [h1]; simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  rw [hrec]; ring

/-- Polynomial times `exp(-x²/2)` is integrable (wrapper around `integrable_eval_mul_exp_neg_mul_sq`). -/
private theorem integrable_hermiteR_mul_gaussian (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * gaussian x) volume := by
  have h : (fun x : ℝ => p.eval x * gaussian x) =
      fun x => p.eval x * Real.exp (-(1/2) * x ^ 2) := by
    ext x; show p.eval x * Real.exp (-(x ^ 2 / 2)) = _; congr 1; congr 1; ring
  rw [h]
  exact integrable_eval_mul_exp_neg_mul_sq p (by positivity : (0:ℝ) < 1/2)

/-- Product of two Hermite polynomials times `exp(-x²/2)` is integrable. -/
private theorem integrable_hermiteProd_mul_gaussian (n m : ℕ) :
    Integrable (fun x : ℝ => (hermiteR n).eval x * (hermiteR m).eval x * gaussian x) volume := by
  have h : (fun x : ℝ => (hermiteR n).eval x * (hermiteR m).eval x * gaussian x) =
      fun x => (hermiteR n * hermiteR m).eval x * gaussian x := by
    ext x; simp [Polynomial.eval_mul, mul_assoc]
  rw [h]
  exact integrable_hermiteR_mul_gaussian (hermiteR n * hermiteR m)

/-- `fun x => Hₙ(x) * (-H_{m+1}(x) * exp(-x²/2))` is integrable. -/
private theorem integrable_hermite_mul_neg_hermite_gaussian (n m : ℕ) :
    Integrable (fun x : ℝ => (hermiteR n).eval x *
      (-(hermiteR (m + 1)).eval x * gaussian x)) volume := by
  have h : (fun x : ℝ => (hermiteR n).eval x * (-(hermiteR (m + 1)).eval x * gaussian x)) =
      fun x => -((hermiteR n * hermiteR (m + 1)).eval x * gaussian x) := by
    ext x; simp [Polynomial.eval_mul]; ring
  rw [h]
  exact (integrable_hermiteR_mul_gaussian (hermiteR n * hermiteR (m + 1))).neg

/-- `Hₘ(x) · exp(-x²/2)` is differentiable. -/
private theorem differentiable_hermiteEval_mul_gaussian (m : ℕ) :
    Differentiable ℝ (fun u => (hermiteR m).eval u * gaussian u) :=
  (hermiteR m).differentiable.mul
    (Differentiable.exp (by fun_prop : Differentiable ℝ (fun u : ℝ => -(u ^ 2 / 2))))

/-- The `J` integral: `∫ Hₙ(x) · Hₘ(x) · exp(-x²/2) dx`. -/
noncomputable def J (n m : ℕ) : ℝ :=
  ∫ x, (hermiteR n).eval x * ((hermiteR m).eval x * gaussian x)

/-- IBP recurrence: `J(n+1, m+1) = (n+1) · J(n, m)`. -/
private theorem J_succ_succ (n m : ℕ) : J (n + 1) (m + 1) = (↑(n + 1) : ℝ) * J n m := by
  unfold J
  -- We use IBP: ∫ f * g' = -∫ f' * g
  -- with f(x) = Hₙ₊₁(x) (polynomial) and g(x) = Hₘ(x)·exp(-x²/2)
  -- g'(x) = -H_{m+1}(x)·exp(-x²/2) (Step 2)
  -- f'(x) = (n+1)·Hₙ(x) (hermite_derivative)
  -- Set up: J(n+1, m+1) = ∫ Hₙ₊₁ · Hₘ₊₁ · G = -∫ Hₙ₊₁ · (d/dx[Hₘ·G])
  have hJ : ∫ x, (hermiteR (n + 1)).eval x * ((hermiteR (m + 1)).eval x * gaussian x) =
      -∫ x, (hermiteR (n + 1)).eval x *
        (deriv (fun u => (hermiteR m).eval u * gaussian u) x) := by
    have h_eq : ∀ x : ℝ, (hermiteR (n + 1)).eval x * ((hermiteR (m + 1)).eval x * gaussian x) =
        -((hermiteR (n + 1)).eval x *
          deriv (fun u => (hermiteR m).eval u * gaussian u) x) := by
      intro x; rw [deriv_hermiteEval_mul_gaussian]; ring
    simp_rw [h_eq, integral_neg]
  rw [hJ]
  -- Apply IBP with v = 1
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (𝕜 := ℝ) (E := ℝ)
    (μ := volume)
    (f := fun x => (hermiteR (n + 1)).eval x)
    (g := fun u => (hermiteR m).eval u * gaussian u)
    (v := (1 : ℝ))
    ?_ ?_ ?_ (fun x _ => (hermiteR (n + 1)).differentiable.differentiableAt)
    (fun x _ => (differentiable_hermiteEval_mul_gaussian m).differentiableAt)
  -- IBP gives: ∫ f * g' = -∫ f' * g
  -- So -∫ f * g' = ∫ f' * g
  simp only [fderiv_apply_one_eq_deriv] at hibp
  rw [neg_eq_iff_eq_neg.mpr hibp]
  -- Simplify deriv of polynomial and factor out constant
  have h_rw : ∀ x : ℝ, deriv (fun x => (hermiteR (n + 1)).eval x) x *
      ((hermiteR m).eval x * gaussian x) =
      (↑(n + 1) : ℝ) * ((hermiteR n).eval x * ((hermiteR m).eval x * gaussian x)) := by
    intro x
    rw [Polynomial.deriv, hermiteR_derivative]
    simp [Polynomial.eval_mul, Polynomial.eval_natCast]; ring
  simp_rw [h_rw, integral_const_mul]
  -- Integrability obligations
  · -- fderiv f · g integrable
    show Integrable (fun x => fderiv ℝ (fun x => (hermiteR (n + 1)).eval x) x 1 *
      ((hermiteR m).eval x * gaussian x)) volume
    have : (fun x => fderiv ℝ (fun x => (hermiteR (n + 1)).eval x) x 1 *
        ((hermiteR m).eval x * gaussian x)) =
        fun x => ((↑(n + 1) : ℝ) * (hermiteR n).eval x) *
          ((hermiteR m).eval x * gaussian x) := by
      ext x
      rw [fderiv_apply_one_eq_deriv, Polynomial.deriv, hermiteR_derivative]
      simp [Polynomial.eval_mul, Polynomial.eval_natCast]
    rw [this]
    have : (fun x => ((↑(n + 1) : ℝ) * (hermiteR n).eval x) *
        ((hermiteR m).eval x * gaussian x)) =
        fun x => (↑(n + 1) : ℝ) * ((hermiteR n).eval x * (hermiteR m).eval x * gaussian x) := by
      ext x; ring
    rw [this]
    exact (integrable_hermiteProd_mul_gaussian n m).const_mul _
  · -- f · fderiv g integrable
    show Integrable (fun x => (hermiteR (n + 1)).eval x *
      (fderiv ℝ (fun u => (hermiteR m).eval u * gaussian u) x 1)) volume
    have : (fun x => (hermiteR (n + 1)).eval x *
        (fderiv ℝ (fun u => (hermiteR m).eval u * gaussian u) x 1)) =
        fun x => (hermiteR (n + 1)).eval x *
          deriv (fun u => (hermiteR m).eval u * gaussian u) x := by
      ext x; rw [fderiv_apply_one_eq_deriv]
    rw [this]
    have : (fun x => (hermiteR (n + 1)).eval x *
        deriv (fun u => (hermiteR m).eval u * gaussian u) x) =
        fun x => (hermiteR (n + 1)).eval x *
          (-(hermiteR (m + 1)).eval x * gaussian x) := by
      ext x; rw [deriv_hermiteEval_mul_gaussian]
    rw [this]
    exact integrable_hermite_mul_neg_hermite_gaussian (n + 1) m
  · -- f · g integrable
    exact (integrable_hermiteProd_mul_gaussian (n + 1) m).congr
      (by filter_upwards; intro x; ring)

/-- Symmetry of the J integral. -/
private theorem J_comm (n m : ℕ) : J n m = J m n := by
  unfold J; congr 1; ext x; ring

/-- Base case: `J(0, 0) = √(2π)`. -/
private theorem J_zero_zero : J 0 0 = Real.sqrt (2 * Real.pi) := by
  unfold J hermiteR
  simp only [hermite_zero]
  have h : (fun x : ℝ => (Polynomial.map (Int.castRingHom ℝ) (C 1)).eval x *
      ((Polynomial.map (Int.castRingHom ℝ) (C 1)).eval x * gaussian x)) =
      fun x => Real.exp (-(1/2) * x ^ 2) := by
    ext x; simp [gaussian]; ring
  rw [h, integral_gaussian (1/2)]
  congr 1; ring

/-- Base case: `J(k+1, 0) = 0` for all k.
    Proof: from `J_succ_succ` and `J_comm`, `(k+2)·J(k+1,0) = J(k+1,0)`, so `(k+1)·J(k+1,0) = 0`. -/
private theorem J_succ_zero (k : ℕ) : J (k + 1) 0 = 0 := by
  -- J(k+2, 1) = (k+2) * J(k+1, 0) by J_succ_succ
  have h1 : J (k + 2) 1 = (↑(k + 2) : ℝ) * J (k + 1) 0 := J_succ_succ (k + 1) 0
  -- J(k+2, 1) = J(1, k+2) = 1 * J(0, k+1) = J(k+1, 0)
  have h2 : J (k + 2) 1 = J (k + 1) 0 := by
    rw [J_comm (k + 2) 1]
    show J 1 (k + 2) = J (k + 1) 0
    rw [show (1 : ℕ) = 0 + 1 from rfl, show k + 2 = (k + 1) + 1 from rfl,
        J_succ_succ 0 (k + 1)]
    simp [J_comm]
  -- So (k+2) * J(k+1, 0) = J(k+1, 0), hence (k+1) * J(k+1, 0) = 0
  have h3 : (↑(k + 1) : ℝ) * J (k + 1) 0 = 0 := by
    have h12 : (↑(k + 2) : ℝ) * J (k + 1) 0 - J (k + 1) 0 = 0 := by linarith
    have : (↑(k + 1) : ℝ) * J (k + 1) 0 =
        (↑(k + 2) : ℝ) * J (k + 1) 0 - J (k + 1) 0 := by push_cast; ring
    linarith
  have h4 : (↑(k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp h3).resolve_left h4

/-- `J(n, m) = if n = m then n! * √(2π) else 0`. -/
theorem J_eq : ∀ m n : ℕ,
    J n m = if n = m then ↑(n.factorial) * Real.sqrt (2 * Real.pi) else 0 := by
  intro m
  induction m with
  | zero =>
    intro n
    cases n with
    | zero => simp [J_zero_zero]
    | succ k => simp [J_succ_zero k]
  | succ m ih =>
    intro n
    cases n with
    | zero =>
      rw [J_comm, J_succ_zero]
      simp
    | succ k =>
      rw [J_succ_succ, ih]
      by_cases h : k = m
      · subst h; simp [Nat.factorial_succ, Nat.cast_mul]; ring
      · simp [h]

lemma hermite_X_mul (n : ℕ) :
    X * hermite (n + 1) = hermite (n + 2) + (↑(n + 1) : ℤ[X]) * hermite n := by
  linear_combination -(hermite_succ (n + 1)) + hermite_derivative n

lemma hermiteR_recurrence_succ (n : ℕ) (t : ℝ) :
    t * (hermiteR (n + 1)).eval t =
    (hermiteR (n + 2)).eval t + ↑(n + 1) * (hermiteR n).eval t := by
  have h := congr_arg (fun p => (Polynomial.map (Int.castRingHom ℝ) p).eval t)
    (hermite_X_mul n)
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast] at h
  linarith

