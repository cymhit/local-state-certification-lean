import LocalCertification.Asymptotic.BlaschkeTermwiseDerivatives
import LocalCertification.Extremal.ElementaryDecay
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
open Filter Metric Set
open scoped BigOperators Topology ContDiff
noncomputable section
namespace LocalCertification.Extremal.GeometricSeries

theorem geometric_derivative_norm_bound (n j : ℕ) (R : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : ‖x‖ ≤ R) :
    ‖iteratedDeriv j (fun t : ℝ => t ^ n) x‖ ≤
      (R ^ j)⁻¹ * ((n : ℝ) ^ j * R ^ n) := by
  rw [iteratedDeriv_pow]
  by_cases hj : j ≤ n
  · have hfac : (n.descFactorial j : ℝ) ≤ (n : ℝ) ^ j := by
      exact_mod_cast Nat.descFactorial_le_pow n j
    have hpow : R ^ j * R ^ (n - j) = R ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    calc
      _ = (n.descFactorial j : ℝ) * ‖x‖ ^ (n - j) := by
        rw [norm_mul, norm_pow]
        simp
      _ ≤ (n : ℝ) ^ j * R ^ (n - j) :=
        mul_le_mul hfac (pow_le_pow_left₀ (norm_nonneg x) hx _) (by positivity) (by positivity)
      _ = _ := by rw [← hpow]; field_simp
  · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr (lt_of_not_ge hj), Nat.cast_zero,
      zero_mul, norm_zero]
    positivity

/-- Geometric domination bounds the derivative series uniformly on each closed subunit ball. -/
theorem geometric_derivative_summable_bound (j : ℕ) (R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    Summable (fun n : ℕ => (R ^ j)⁻¹ * ((n : ℝ) ^ j * R ^ n)) := by
  have hs := (summable_norm_pow_mul_geometric_of_norm_lt_one j
    (show ‖R‖ < 1 by simpa only [Real.norm_eq_abs, abs_of_pos hR] using hR1)).of_norm
  exact hs.mul_left _

/-- Actual repeated termwise differentiation of the geometric series. -/
theorem geometric_iteratedDeriv_eq_tsum (r : ℕ) (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    iteratedDeriv r (fun x : ℝ => (1 - x)⁻¹) z =
      ∑' n : ℕ, iteratedDeriv r (fun x : ℝ => x ^ n) z := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz1
  have hR : 0 < R := hz.trans hzR
  have hzin : z ∈ ball (0 : ℝ) R := by simpa [Real.dist_eq, abs_of_pos hz] using hzR
  have hterm (n j : ℕ) (x : ℝ) : ContDiffAt ℝ (j : ℕ∞ω) (fun t : ℝ => t ^ n) x := by
    fun_prop
  have heq (j n : ℕ) (x : ℝ) (hx : x ∈ ball (0 : ℝ) R) :
      iteratedDerivWithin j (fun t : ℝ => t ^ n) (ball 0 R) x =
        iteratedDeriv j (fun t : ℝ => t ^ n) x :=
    iteratedDerivWithin_eq_iteratedDeriv isOpen_ball.uniqueDiffOn (hterm n j x) hx
  have hsum (x : ℝ) (hx : x ∈ ball (0 : ℝ) R) : Summable (fun n : ℕ => x ^ n) :=
    (hasSum_geometric_of_norm_lt_one ((by simpa using hx : ‖x‖ < R).trans hR1)).summable
  have hunif (j : ℕ) : SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin j (fun t : ℝ => t ^ n) (ball 0 R)) (ball 0 R) := by
    have h : HasSumUniformlyOn
        (fun n => iteratedDerivWithin j (fun t : ℝ => t ^ n) (ball 0 R))
        (fun x => ∑' n, iteratedDerivWithin j (fun t : ℝ => t ^ n) (ball 0 R) x) (ball 0 R) := by
      apply HasSumUniformlyOn.of_norm_le_summable (geometric_derivative_summable_bound j R hR hR1)
      intro n x hx
      rw [heq j n x hx]
      have hxR : ‖x‖ < R := by simpa using hx
      exact geometric_derivative_norm_bound n j R hR x hxR.le
    exact h.hasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  have hdiff (n j : ℕ) (x : ℝ) (hx : x ∈ ball (0 : ℝ) R) :
      DifferentiableAt ℝ (iteratedDerivWithin j (fun t : ℝ => t ^ n) (ball 0 R)) x := by
    have hd : DifferentiableAt ℝ (iteratedDeriv j (fun t : ℝ => t ^ n)) x := by
      have hf : iteratedDeriv j (fun t : ℝ => t ^ n) =
          (fun t : ℝ => (n.descFactorial j : ℝ) * t ^ (n - j)) :=
        funext (fun t => iteratedDeriv_pow n j)
      rw [hf]
      fun_prop
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hx] with t ht
    exact heq j n t ht
  have h := iteratedDerivWithin_tsum r isOpen_ball hzin hsum
    (fun j _ _ => hunif j) (fun n j x _ hx => hdiff n j x hx)
  have hsumeq : (ball (0 : ℝ) R).EqOn (fun x => ∑' n : ℕ, x ^ n)
      (fun x => (1 - x)⁻¹) := fun x hx =>
    (hasSum_geometric_of_norm_lt_one ((by simpa using hx : ‖x‖ < R).trans hR1)).tsum_eq
  have hcd : ContDiffAt ℝ (r : ℕ∞ω) (fun x : ℝ => (1 - x)⁻¹) z := by
    have hne : 1 - z ≠ 0 := by linarith
    convert
      (contDiffAt_const.div (contDiffAt_const.sub contDiffAt_id) hne :
        ContDiffAt ℝ (r : ℕ∞ω) (fun x : ℝ => 1 / (1 - x)) z) using 1
    funext x
    simp
  calc
    _ = iteratedDerivWithin r (fun x : ℝ => (1 - x)⁻¹) (ball 0 R) z :=
      (iteratedDerivWithin_eq_iteratedDeriv isOpen_ball.uniqueDiffOn hcd hzin).symm
    _ = iteratedDerivWithin r (fun x => ∑' n : ℕ, x ^ n) (ball 0 R) z :=
      (iteratedDerivWithin_congr hsumeq hzin).symm
    _ = ∑' n, iteratedDerivWithin r (fun t : ℝ => t ^ n) (ball 0 R) z := h
    _ = _ := tsum_congr (fun n => heq r n z hzin)

theorem geometric_iteratedDeriv_value (r : ℕ) (z : ℝ) (hz : z < 1) :
    iteratedDeriv r (fun x : ℝ => (1 - x)⁻¹) z = (r.factorial : ℝ) / (1 - z) ^ (r + 1) := by
  induction r generalizing z with
  | zero => simp [one_div]
  | succ r ih =>
    have heq : iteratedDeriv r (fun x : ℝ => (1 - x)⁻¹) =ᶠ[𝓝 z]
        (fun x : ℝ => (r.factorial : ℝ) / (1 - x) ^ (r + 1)) := by
      filter_upwards [isOpen_Iio.mem_nhds hz] with x hx
      exact ih x hx
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hne : 1 - z ≠ 0 := by linarith
    have hd := (hasDerivAt_const z (r.factorial : ℝ)).div
      (((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)).pow (r + 1))
      (pow_ne_zero _ hne)
    change HasDerivAt (fun x : ℝ => (r.factorial : ℝ) / (1 - x) ^ (r + 1)) _ z at hd
    rw [hd.deriv]
    dsimp only [Pi.pow_apply, Pi.sub_apply, id_eq]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
      zero_sub, zero_mul, pow_succ]
    field_simp

theorem geometric_derivative_hasSum (r : ℕ) (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    HasSum (fun n : ℕ => (n.descFactorial r : ℝ) * z ^ (n - r))
      ((r.factorial : ℝ) / (1 - z) ^ (r + 1)) := by
  obtain ⟨R, hzR, hR1⟩ := exists_between hz1
  have hR : 0 < R := hz.trans hzR
  have hs : Summable (fun n : ℕ => iteratedDeriv r (fun x : ℝ => x ^ n) z) := by
    apply Summable.of_norm_bounded (geometric_derivative_summable_bound r R hR hR1)
    intro n
    exact geometric_derivative_norm_bound n r R hR z (by simpa [Real.norm_eq_abs, abs_of_pos hz] using hzR.le)
  have h := hs.hasSum
  rw [← geometric_iteratedDeriv_eq_tsum r z hz hz1, geometric_iteratedDeriv_value r z hz1] at h
  simpa only [iteratedDeriv_pow] using h

/-- The precise binomial generating function, derived by r termwise differentiations. -/
theorem hasSum_choose_mul_geometric_via_derivatives (r : ℕ) (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    HasSum (fun n : ℕ => ((n + r).choose r : ℝ) * z ^ n) (1 / (1 - z) ^ (r + 1)) := by
  have hs := geometric_derivative_hasSum r z hz hz1
  have hpre : (∑ i ∈ Finset.range r, (i.descFactorial r : ℝ) * z ^ (i - r)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hi)]
  have hshift := (hasSum_nat_add_iff'
    (f := fun n : ℕ => (n.descFactorial r : ℝ) * z ^ (n - r)) r).mpr hs
  rw [hpre, sub_zero] at hshift
  have h := hshift.mul_left ((r.factorial : ℝ)⁻¹)
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  convert h using 1
  · funext n
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.add_sub_cancel]
    field_simp
  · field_simp

end LocalCertification.Extremal.GeometricSeries
