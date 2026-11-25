import LocalCertification.Extremal.DegreeZero
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Fin.Basic

set_option autoImplicit false
open scoped BigOperators Topology ContDiff
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- Repeated Rolle on arbitrary strictly ordered finite zeros. -/
theorem exists_iteratedDeriv_zero_of_zeros (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Fin (n+1) → ℝ) (hx : StrictMono x)
    (hz : ∀ i, f (x i) = 0) : ∃ y, iteratedDeriv n f y = 0 := by
  induction n generalizing f with
  | zero => exact ⟨x 0, by simpa using hz 0⟩
  | succ n ih =>
    have hex (i : Fin (n+1)) : ∃ y ∈ Ioo (x i.castSucc) (x i.succ), deriv f y = 0 :=
      exists_deriv_eq_zero (hx (show i.castSucc < i.succ from Fin.castSucc_lt_succ)) hf.continuous.continuousOn
        ((hz i.castSucc).trans (hz i.succ).symm)
    choose y hy hyzero using hex
    have hymono : StrictMono y := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      calc
        y i.castSucc < x i.castSucc.succ := (hy i.castSucc).2
        _ = x i.succ.castSucc := by congr 1
        _ < y i.succ := (hy i.succ).1
    obtain ⟨z, hz⟩ := ih (contDiff_infty_iff_deriv.mp hf).2 y hymono hyzero
    exact ⟨z, by simpa only [iteratedDeriv_succ'] using hz⟩

theorem iteratedDeriv_polynomial_eval (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (Polynomial.derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun x => p.eval x) = fun x => p.derivative.eval x := funext (fun x => p.deriv)
    rw [hd, ih]
    simp only [Function.iterate_succ_apply]

theorem polynomial_eval_contDiff (p : ℝ[X]) (n : WithTop ℕ∞) : ContDiff ℝ n (fun x => p.eval x) := by
  simpa using p.contDiff_aeval (𝕜 := ℝ) n

/-- Exponential plus polynomial after multiplying the original G by q^x. -/
def expPolynomial (a h : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ := h * Real.exp (a*x) + p.eval x

theorem expPolynomial_contDiff (a h : ℝ) (p : ℝ[X]) (n : WithTop ℕ∞) :
    ContDiff ℝ n (expPolynomial a h p) :=
  (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).add
    (polynomial_eval_contDiff p n)

theorem iteratedDeriv_expPolynomial (n : ℕ) (a h : ℝ) (p : ℝ[X]) (x : ℝ) :
    iteratedDeriv n (expPolynomial a h p) x =
      h * (a^n * Real.exp (a*x)) + (Polynomial.derivative^[n] p).eval x := by
  change iteratedDeriv n (fun x => h * Real.exp (a*x) + p.eval x) x = _
  rw [iteratedDeriv_fun_add
    (show ContDiffAt ℝ n (fun x => h * Real.exp (a*x)) x from (by fun_prop))
    (polynomial_eval_contDiff p n).contDiffAt]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul, iteratedDeriv_polynomial_eval]

/-- A nonzero exponential term plus a degree-r polynomial cannot vanish at r+2 ordered points. -/
theorem expPolynomial_not_many_zeros (r : ℕ) (a h : ℝ) (p : ℝ[X])
    (ha : a ≠ 0) (hh : h ≠ 0) (hp : p.natDegree ≤ r)
    (x : Fin (r+2) → ℝ) (hx : StrictMono x) : ¬∀ i, expPolynomial a h p (x i) = 0 := by
  intro hz
  obtain ⟨y, hy⟩ := exists_iteratedDeriv_zero_of_zeros (r+1)
    (expPolynomial_contDiff a h p ∞) x hx hz
  rw [iteratedDeriv_expPolynomial, Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_of_le hp)] at hy
  simp only [Polynomial.eval_zero, add_zero] at hy
  exact (mul_ne_zero hh (mul_ne_zero (pow_ne_zero _ ha) (Real.exp_ne_zero _))) hy

end LocalCertification.Extremal
