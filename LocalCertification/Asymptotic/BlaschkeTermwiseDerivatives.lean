import LocalCertification.Asymptotic.BlaschkeUniformSeries

set_option autoImplicit false
open Filter Metric Set
open scoped BigOperators Topology ContDiff
noncomputable section
namespace LocalCertification.Asymptotic

/-- Every iterated derivative of the actual rational power is the sum of the actual differentiated
monomials on a disk strictly surrounding the unit circle. -/
theorem blaschke_iteratedDeriv_eq_tsum (a : ℝ) (s k : ℕ) (R T : ℝ)
    (hR : 1≤R) (hRT : R<T) (hTa : |a| * T<1) (z : ℂ) (hz : z∈ball 0 R) :
    iteratedDeriv k (fun w => blaschke a w^s) z=
      ∑' n,iteratedDeriv k (blaschkeSeriesTerm a s n) z := by
  have hzR : ‖z‖<R := by simpa using hz
  have hin (w : ℂ) (hw : w∈ball 0 R) : ‖(a:ℂ)*w‖<1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hwR : ‖w‖<R := by simpa using hw
    exact (mul_le_mul_of_nonneg_left (hwR.trans hRT).le (abs_nonneg a)).trans_lt hTa
  have hterm (n j : ℕ) (w : ℂ) : ContDiffAt ℂ (j:ℕ∞ω) (blaschkeSeriesTerm a s n) w := by
    unfold blaschkeSeriesTerm
    fun_prop
  have heq (j n : ℕ) (w : ℂ) (hw : w∈ball 0 R) :
      iteratedDerivWithin j (blaschkeSeriesTerm a s n) (ball 0 R) w=
        iteratedDeriv j (blaschkeSeriesTerm a s n) w :=
    iteratedDerivWithin_eq_iteratedDeriv isOpen_ball.uniqueDiffOn (hterm n j w) hw
  have hsum (w : ℂ) (hw : w∈ball 0 R) : Summable (fun n => blaschkeSeriesTerm a s n w) :=
    (blaschkeCoeff_hasSum a s w (hin w hw)).summable
  have hunif (j : ℕ) : SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin j (blaschkeSeriesTerm a s n) (ball 0 R)) (ball 0 R) := by
    have h : HasSumUniformlyOn
        (fun n => iteratedDerivWithin j (blaschkeSeriesTerm a s n) (ball 0 R))
        (fun w => ∑' n,iteratedDerivWithin j (blaschkeSeriesTerm a s n) (ball 0 R) w) (ball 0 R) := by
      apply HasSumUniformlyOn.of_norm_le_summable
        (blaschkeCoeff_weighted_radius_summable a s j R T (by linarith) hRT hTa)
      intro n w hw
      rw [heq j n w hw]
      have hwR : ‖w‖ < R := by simpa using hw
      exact blaschkeSeriesTerm_derivative_norm_le a s n j R hR w hwR.le
    exact h.hasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  have hdiff (n j : ℕ) (w : ℂ) (hw : w∈ball 0 R) :
      DifferentiableAt ℂ (iteratedDerivWithin j (blaschkeSeriesTerm a s n) (ball 0 R)) w := by
    have hd : DifferentiableAt ℂ (iteratedDeriv j (blaschkeSeriesTerm a s n)) w := by
      have hf : iteratedDeriv j (blaschkeSeriesTerm a s n)=
          fun v => (blaschkeCoeff a s n:ℂ)*(n.descFactorial j:ℂ)*v^(n-j) :=
        funext (blaschkeSeriesTerm_iteratedDeriv a s n j)
      rw [hf]
      fun_prop
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hw] with v hv
    exact heq j n v hv
  have h := iteratedDerivWithin_tsum k isOpen_ball hz hsum
    (fun j _ _ => hunif j) (fun n j w _ hw => hdiff n j w hw)
  have hsumeq : (ball (0:ℂ) R).EqOn (fun w => ∑' n,blaschkeSeriesTerm a s n w)
      (fun w => blaschke a w^s) := fun w hw => (blaschkeCoeff_hasSum a s w (hin w hw)).tsum_eq
  have hcd : ContDiffAt ℂ (k:ℕ∞ω) (fun w => blaschke a w^s) z := by
    unfold blaschke
    exact ((contDiffAt_const.sub contDiffAt_id).div
      (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id))
      (blaschke_denominator_ne_zero a z (hin z hz))).pow s
  calc
    _=iteratedDerivWithin k (fun w => blaschke a w^s) (ball 0 R) z :=
      (iteratedDerivWithin_eq_iteratedDeriv isOpen_ball.uniqueDiffOn hcd hz).symm
    _=iteratedDerivWithin k (fun w => ∑' n,blaschkeSeriesTerm a s n w) (ball 0 R) z :=
      (iteratedDerivWithin_congr hsumeq hz).symm
    _=∑' n,iteratedDerivWithin k (blaschkeSeriesTerm a s n) (ball 0 R) z := h
    _=_ := tsum_congr (fun n => heq k n z hz)

/-- Actual derivative sums and absolute convergence on the unit circle, for every order including zero. -/
theorem blaschke_derivative_circle_hasSum (a : ℝ) (ha : |a|<1) (s k : ℕ)
    (z : ℂ) (hz : ‖z‖=1) :
    HasSum (fun n => (blaschkeCoeff a s n:ℂ)*(n.descFactorial k:ℂ)*z^(n-k))
      (iteratedDeriv k (fun w => blaschke a w^s) z) ∧
    Summable (fun n => ‖(blaschkeCoeff a s n:ℂ)*(n.descFactorial k:ℂ)*z^(n-k)‖) := by
  obtain ⟨R,T,hR,hRT,hTa⟩ := blaschke_uniform_radii a ha
  have hb : z∈ball (0:ℂ) R := by simpa [hz] using hR
  have hnorm := blaschke_derivative_series_summable_norm a s k R T hR.le hRT hTa z (by linarith)
  have he := blaschke_iteratedDeriv_eq_tsum a s k R T hR.le hRT hTa z hb
  constructor
  · rw [he]
    simpa only [blaschkeSeriesTerm_iteratedDeriv] using hnorm.of_norm.hasSum
  · simpa only [blaschkeSeriesTerm_iteratedDeriv] using hnorm

/-- Every derivative series converges uniformly to the corresponding true derivative on the unit
circle. The limit is the rational Blaschke power derivative, not a merely defined coefficient sum. -/
theorem blaschke_all_derivatives_uniform_circle (a : ℝ) (ha : |a|<1) (s k : ℕ) :
    HasSumUniformlyOn (fun n z => (blaschkeCoeff a s n:ℂ)*(n.descFactorial k:ℂ)*z^(n-k))
      (iteratedDeriv k (fun z => blaschke a z^s)) (sphere 0 1) := by
  have h := (blaschke_derivative_series_uniform_circle a ha s k).2
  simp only [blaschkeSeriesTerm_iteratedDeriv] at h
  apply h.congr_right
  intro z hz
  exact (blaschke_derivative_circle_hasSum a ha s k z (by simpa using hz)).1.tsum_eq

/-- The natural Taylor partial sums, differentiated term by term to any fixed order, converge
uniformly to the true derivative on the unit circle. -/
theorem blaschke_derivative_partialSums_uniform_circle (a : ℝ) (ha : |a|<1) (s k : ℕ) :
    TendstoUniformlyOn (fun N z => ∑ n∈Finset.range N,
      (blaschkeCoeff a s n:ℂ)*(n.descFactorial k:ℂ)*z^(n-k))
      (iteratedDeriv k (fun z => blaschke a z^s)) atTop (sphere 0 1) :=
  (blaschke_all_derivatives_uniform_circle a ha s k).tendstoUniformlyOn_finsetRange

/-- The paper's actual parameter a=q⁻¹: every differentiated series is absolutely and uniformly
convergent to the rational-power derivative, including s=0 and derivative order zero. -/
theorem reciprocal_blaschke_all_derivatives (q : ℝ) (hq : 1<q) (s k : ℕ) :
    (∀ z : ℂ,‖z‖=1 →
      HasSum (fun n => (blaschkeCoeff q⁻¹ s n:ℂ)*(n.descFactorial k:ℂ)*z^(n-k))
        (iteratedDeriv k (fun w => blaschke q⁻¹ w^s) z) ∧
      Summable (fun n => ‖(blaschkeCoeff q⁻¹ s n:ℂ)*(n.descFactorial k:ℂ)*z^(n-k)‖)) ∧
    TendstoUniformlyOn (fun N z => ∑ n∈Finset.range N,
      (blaschkeCoeff q⁻¹ s n:ℂ)*(n.descFactorial k:ℂ)*z^(n-k))
      (iteratedDeriv k (fun z => blaschke q⁻¹ z^s)) atTop (sphere 0 1) := by
  have ha : |q⁻¹|<1 := by
    rw [abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hq
  exact ⟨blaschke_derivative_circle_hasSum q⁻¹ ha s k,
    blaschke_derivative_partialSums_uniform_circle q⁻¹ ha s k⟩

end LocalCertification.Asymptotic
