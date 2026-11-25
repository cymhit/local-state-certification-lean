import LocalCertification.Asymptotic.BlaschkeCoefficients
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

set_option autoImplicit false
open Filter Metric Set
open scoped BigOperators Topology ContDiff
noncomputable section
namespace LocalCertification.Asymptotic

/-- A polynomial weight remains absolutely summable on any strictly smaller concentric disk. -/
theorem blaschkeCoeff_weighted_radius_summable (a : ℝ) (s k : ℕ) (R T : ℝ)
    (hR : 0≤R) (hRT : R<T) (hTa : |a| *T<1) :
    Summable (fun n : ℕ => (n:ℝ)^k*|blaschkeCoeff a s n| *R^n) := by
  have hT : 0<T := hR.trans_lt hRT
  have hc : Summable (fun n => |blaschkeCoeff a s n| *T^n) := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow,abs_of_pos hT] using
      blaschkeCoeff_summable_norm a s (T:ℂ) (by simpa [norm_mul,abs_of_pos hT] using hTa)
  let M := ∑' n,|blaschkeCoeff a s n| *T^n
  have hb (n : ℕ) : |blaschkeCoeff a s n| *T^n≤M :=
    hc.le_tsum n (fun _ _ => by positivity)
  have hg : Summable (fun n : ℕ => (n:ℝ)^k*(R/T)^n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hR hT.le)]
      exact (div_lt_one hT).mpr hRT)
  apply (hg.mul_left M).of_nonneg_of_le (fun _ => by positivity)
  intro n
  calc
    (n:ℝ)^k*|blaschkeCoeff a s n| *R^n=
        ((n:ℝ)^k*(|blaschkeCoeff a s n| *T^n))*(R/T)^n := by
      rw [div_pow]
      field_simp
    _≤((n:ℝ)^k*M)*(R/T)^n := by gcongr;exact hb n
    _=M*((n:ℝ)^k*(R/T)^n) := by ring

/-- Each summand is the actual monomial of the existing real Blaschke coefficients. -/
def blaschkeSeriesTerm (a : ℝ) (s n : ℕ) (z : ℂ) : ℂ :=
  (blaschkeCoeff a s n:ℂ)*z^n

theorem blaschkeSeriesTerm_iteratedDeriv (a : ℝ) (s n k : ℕ) (z : ℂ) :
    iteratedDeriv k (blaschkeSeriesTerm a s n) z=
      (blaschkeCoeff a s n:ℂ)*(n.descFactorial k:ℂ)*z^(n-k) := by
  change iteratedDeriv k (fun w : ℂ => (blaschkeCoeff a s n:ℂ)*w^n) z=_
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_pow]
  ring

/-- A common summable majorant controls every derivative on the whole closed disk. -/
theorem blaschkeSeriesTerm_derivative_norm_le (a : ℝ) (s n k : ℕ) (R : ℝ) (hR : 1≤R)
    (z : ℂ) (hz : ‖z‖≤R) :
    ‖iteratedDeriv k (blaschkeSeriesTerm a s n) z‖≤
      (n:ℝ)^k*|blaschkeCoeff a s n| *R^n := by
  rw [blaschkeSeriesTerm_iteratedDeriv,norm_mul,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
  have hd : (n.descFactorial k:ℝ)≤(n:ℝ)^k := by exact_mod_cast Nat.descFactorial_le_pow n k
  calc
    _≤|blaschkeCoeff a s n| *(n:ℝ)^k*R^(n-k) := by gcongr
    _≤|blaschkeCoeff a s n| *(n:ℝ)^k*R^n := by
      gcongr
      exact Nat.sub_le n k
    _=_ := by ring

/-- Derivative series of every order are absolutely summable, uniformly majorized on a closed disk. -/
theorem blaschke_derivative_series_summable_norm (a : ℝ) (s k : ℕ) (R T : ℝ)
    (hR : 1≤R) (hRT : R<T) (hTa : |a| *T<1) (z : ℂ) (hz : ‖z‖≤R) :
    Summable (fun n => ‖iteratedDeriv k (blaschkeSeriesTerm a s n) z‖) :=
  (blaschkeCoeff_weighted_radius_summable a s k R T (by linarith) hRT hTa).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => blaschkeSeriesTerm_derivative_norm_le a s n k R hR z hz)

theorem blaschke_derivative_series_uniform (a : ℝ) (s k : ℕ) (R T : ℝ)
    (hR : 1≤R) (hRT : R<T) (hTa : |a| *T<1) :
    HasSumUniformlyOn (fun n z => iteratedDeriv k (blaschkeSeriesTerm a s n) z)
      (fun z => ∑' n,iteratedDeriv k (blaschkeSeriesTerm a s n) z) (closedBall 0 R) := by
  apply HasSumUniformlyOn.of_norm_le_summable
    (blaschkeCoeff_weighted_radius_summable a s k R T (by linarith) hRT hTa)
  intro n z hz
  exact blaschkeSeriesTerm_derivative_norm_le a s n k R hR z (by simpa using hz)

/-- Actual analytic radii surround the unit circle whenever the Blaschke pole lies outside it. -/
theorem blaschke_uniform_radii (a : ℝ) (ha : |a|<1) :
    ∃ R T : ℝ,1<R ∧ R<T ∧ |a| *T<1 := by
  let T := 2/(1+|a|)
  have hden : 0<1+|a| := by positivity
  have hT : 1<T := (lt_div_iff₀ hden).mpr (by linarith)
  have hTa : |a| *T<1 := by
    dsimp [T]
    rw [← mul_div_assoc]
    exact (div_lt_one hden).mpr (by linarith)
  exact ⟨(1+T)/2,T,by linarith,by linarith,hTa⟩

/-- The paper's absolute and uniform convergence of all derivative series on the unit circle. -/
theorem blaschke_derivative_series_uniform_circle (a : ℝ) (ha : |a|<1) (s k : ℕ) :
    (∀ z : ℂ,‖z‖=1 → Summable (fun n => ‖iteratedDeriv k (blaschkeSeriesTerm a s n) z‖)) ∧
    HasSumUniformlyOn (fun n z => iteratedDeriv k (blaschkeSeriesTerm a s n) z)
      (fun z => ∑' n,iteratedDeriv k (blaschkeSeriesTerm a s n) z) (sphere 0 1) := by
  obtain ⟨R,T,hR,hRT,hTa⟩ := blaschke_uniform_radii a ha
  refine ⟨fun z hz => blaschke_derivative_series_summable_norm a s k R T hR.le hRT hTa z (by linarith),?_⟩
  apply (blaschke_derivative_series_uniform a s k R T hR.le hRT hTa).mono
  intro z hz
  simpa only [mem_closedBall,dist_zero_right] using (show ‖z‖≤R by
    have : ‖z‖=1 := by simpa using hz
    linarith)

end LocalCertification.Asymptotic
