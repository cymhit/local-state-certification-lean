import CertificationGaussian.Radial
import CertificationGaussian.KernelAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace CertificationGaussian

/-- Any fixed polynomial prefactor is eventually absorbed by a positive linear exponential. -/
theorem eventually_polynomial_le_exp (C : ℝ) (k : Nat) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n : Nat in atTop, C * (n:ℝ)^k ≤ Real.exp (b * n) := by
  have h := ((isLittleO_pow_exp_pos_mul_atTop k hb).const_mul_left C).eventuallyLE
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  filter_upwards [hn] with n hn
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hn)

theorem sqrt_dimension_eq_exp {d : Nat} (hd : 0 < d) (n : Nat) :
    Real.sqrt ((d:ℝ)^n) = Real.exp ((Real.log d / 2) * n) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  have he : (d:ℝ)^n = Real.exp ((n:ℝ) * Real.log d) := by
    rw [Real.exp_nat_mul, Real.exp_log hdR]
  rw [he]
  congr 1
  norm_num
  ring

/-- A polynomial divided by sqrt(d^n), raised to n², has a dimension-uniform cubic exponential bound. -/
theorem eventually_polynomial_gaussian_cubic {d : Nat} (hd : 2 ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (k : Nat) :
    ∀ᶠ n : Nat in atTop,
      (C * (n:ℝ)^k / Real.sqrt ((d:ℝ)^n)) ^ ((n:ℝ)^2) ≤
        Real.exp (-(Real.log d / 4) * (n:ℝ)^3) := by
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  have hb : 0 < Real.log d / 4 := div_pos (Real.log_pos hdR) (by norm_num)
  filter_upwards [eventually_polynomial_le_exp C k hb] with n hn
  have hbase : C * (n:ℝ)^k / Real.sqrt ((d:ℝ)^n) ≤ Real.exp (-(Real.log d / 4) * n) := by
    rw [sqrt_dimension_eq_exp (by omega)]
    calc
      _ ≤ Real.exp ((Real.log d / 4) * n) / Real.exp ((Real.log d / 2) * n) := by
        exact div_le_div_of_nonneg_right hn (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  calc
    _ ≤ (Real.exp (-(Real.log d / 4) * n)) ^ ((n:ℝ)^2) :=
      Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = _ := by rw [← Real.exp_mul]; congr 1; ring

/-- A deliberately coarse natural-power estimate avoids any half-integer support exponent. -/
theorem reciprocal_sqrt_le_of_power_lower {c v x : ℝ} {s : Nat}
    (hc : 0 < c) (hx : 1 ≤ x) (hv : c / x^s ≤ v) :
    1 / Real.sqrt v ≤ x^s / Real.sqrt c := by
  have hx0 : 0 < x := by linarith
  have hp : 1 ≤ x^s := one_le_pow₀ hx
  have hv0 : 0 < v := (div_pos hc (pow_pos hx0 _)).trans_le hv
  have hcv : c ≤ v * x^s := (div_le_iff₀ (pow_pos hx0 _)).mp hv
  have hcv2 : c ≤ v * (x^s)^2 := hcv.trans
    (mul_le_mul_of_nonneg_left (by nlinarith) hv0.le)
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hv0) (Real.sqrt_pos.mpr hc)).mpr
  rw [one_mul]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hv0.le]
  nlinarith

/-- The actual relative-quartic Markov prefactor is bounded by a fixed polynomial over sqrt(D). -/
theorem relative_quartic_prefactor_le {c v x D L : ℝ} {s : Nat}
    (hc : 0 < c) (hx : 1 ≤ x) (hD : 0 < D) (hL : 0 ≤ L) (hv : c / x^s ≤ v) :
    5*(x^2-1)^2 * Real.sqrt (8*L^2*v/D) / (v/x) ≤
      (5*Real.sqrt 8*L/Real.sqrt c) * x^(s+5) / Real.sqrt D := by
  have hx0 : 0 < x := by linarith
  have hv0 : 0 < v := (div_pos hc (pow_pos hx0 _)).trans_le hv
  have hsq : (x^2-1)^2 ≤ x^4 := by nlinarith [sq_nonneg (x^2-1)]
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8), Real.sqrt_sq hL]
  calc
    _ = (5*(x^2-1)^2 * Real.sqrt 8*L*x/Real.sqrt D) * (Real.sqrt v/v) := by field_simp
    _ = (5*(x^2-1)^2 * Real.sqrt 8*L*x/Real.sqrt D) * (1/Real.sqrt v) := by
      rw [Real.sqrt_div_self']
    _ ≤ (5*(x^2-1)^2 * Real.sqrt 8*L*x/Real.sqrt D) * (x^s/Real.sqrt c) :=
      mul_le_mul_of_nonneg_left (reciprocal_sqrt_le_of_power_lower hc hx hv) (by positivity)
    _ ≤ (5*x^4 * Real.sqrt 8*L*x/Real.sqrt D) * (x^s/Real.sqrt c) := by gcongr
    _ = _ := by rw [pow_add]; ring

/-- The common radial prefactor has a degree-six polynomial bound. -/
theorem radial_prefactor_le {x D : ℝ} (hx : 1 ≤ x) (hD : 0 < D) :
    5*(x^2-1)^2 * Real.sqrt D⁻¹ / (x^2)⁻¹ ≤ 5*x^6/Real.sqrt D := by
  have hsq : (x^2-1)^2 ≤ x^4 := by nlinarith [sq_nonneg (x^2-1)]
  rw [Real.sqrt_inv, div_inv_eq_mul]
  calc
    _ ≤ 5*x^4 * (Real.sqrt D)⁻¹ * x^2 := by gcongr
    _ = _ := by ring

/-- The same eventual threshold works for every unitary basis in dimension d^n. -/
theorem quditQuartic_eventually_cubic {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : Nat in atTop, ∀ U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ,
      U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) →
      (pairedGaussian (QuditIndex d n))
        {x | kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ U x|} ≤
      ENNReal.ofReal (Real.exp (-(Real.log d / 4) * (n:ℝ)^3)) := by
  let c := kernelOrderLowerConstant d J θ hθ
  let s := effectiveKernelOrder J θ hθ
  let C := 5*Real.sqrt 8*kernelWeightL1 J θ/Real.sqrt c
  have hc : 0 < c := kernelOrderLowerConstant_pos hd J θ hθ
  have hL := kernelWeightL1_nonneg J θ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_polynomial_gaussian_cubic hd hC (s+5),
    eventually_ge_atTop (max 2 (2*J.sup id))] with n hbound hn
  intro U hU
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hN : max 1 (2*J.sup id) ≤ n := by omega
  have hJ : ∀ k ∈ J, k ≤ n := by
    intro k hk
    have hk' : k ≤ J.sup id := Finset.le_sup (f := id) hk
    have ht := (le_max_right 2 (2*J.sup id)).trans hn
    omega
  have hv := (kernelVarianceScale_order_bounds hd J θ hθ hN).1
  have hv0 := kernelVarianceScale_pos hd J hJ θ hθ
  have hD : (0:ℝ) < (d:ℝ)^n := by positivity
  have hpref := relative_quartic_prefactor_le hc (show (1:ℝ) ≤ n by linarith) hD hL hv
  calc
    _ ≤ ENNReal.ofReal ((5*((n:ℝ)^2-1)^2 * Real.sqrt
        (8*(kernelWeightL1 J θ)^2*kernelVarianceScale d n J θ/(d:ℝ)^n) /
        (kernelVarianceScale d n J θ/n))^((n:ℝ)^2)) :=
      quditQuartic_abs_tail hd J hJ θ U hU ((n:ℝ)^2) (by nlinarith)
        (kernelVarianceScale d n J θ/n) (by positivity)
    _ ≤ ENNReal.ofReal ((C*(n:ℝ)^(s+5)/Real.sqrt ((d:ℝ)^n))^((n:ℝ)^2)) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow (by positivity) hpref (by positivity)
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

/-- The actual single common-radius event also has a cubic exponential bound. -/
theorem quditRadius_eventually_cubic {d : Nat} (hd : 2 ≤ d) :
    ∀ᶠ n : Nat in atTop,
      (pairedGaussian (QuditIndex d n))
        {x | ((n:ℝ)^2)⁻¹ ≤ |gaussianRadius (QuditIndex d n) x - 1|} ≤
      ENNReal.ofReal (Real.exp (-(Real.log d / 4) * (n:ℝ)^3)) := by
  filter_upwards [eventually_polynomial_gaussian_cubic hd (show (0:ℝ) ≤ 5 by norm_num) 6,
    eventually_ge_atTop 2] with n hbound hn
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0:ℝ) < (d:ℝ)^n := by positivity
  calc
    _ ≤ ENNReal.ofReal ((5*((n:ℝ)^2-1)^2 * Real.sqrt ((d:ℝ)^n)⁻¹ /
        ((n:ℝ)^2)⁻¹)^((n:ℝ)^2)) := qudit_common_radius_tail hd hn
    _ ≤ ENNReal.ofReal ((5*(n:ℝ)^6/Real.sqrt ((d:ℝ)^n))^((n:ℝ)^2)) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow (by positivity) (radial_prefactor_le (by linarith) hD) (by positivity)
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

/-- A finite family uses only a union bound; neither independence nor nonnegative kernel weights is assumed. -/
theorem quditQuartic_eventually_finite_union {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : Nat in atTop,
      ∀ S : Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ),
      (∀ U ∈ S, U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) →
      (pairedGaussian (QuditIndex d n))
        {x | ∃ U ∈ S, kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ U x|} ≤
      ENNReal.ofReal ((S.card:ℝ) * Real.exp (-(Real.log d / 4) * (n:ℝ)^3)) := by
  classical
  filter_upwards [quditQuartic_eventually_cubic hd J θ hθ] with n hn
  intro S hS
  have he : {x | ∃ U ∈ S, kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ U x|} =
      ⋃ U ∈ S, {x | kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ U x|} := by
    ext x
    simp
  rw [he]
  calc
    _ ≤ ∑ U ∈ S, (pairedGaussian (QuditIndex d n))
        {x | kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ U x|} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _U ∈ S, ENNReal.ofReal (Real.exp (-(Real.log d / 4) * (n:ℝ)^3)) :=
      Finset.sum_le_sum (fun U hU => hn U (hS U hU))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

/-- Quadratic log-cardinality is strictly below the already proved cubic decay. -/
theorem eventually_quadratic_exp_mul_cubic {a : ℝ} (ha : 0 < a) (K : ℝ) :
    ∀ᶠ n : Nat in atTop,
      Real.exp (K*(n:ℝ)^2) * Real.exp (-a*(n:ℝ)^3) ≤
        Real.exp (-(a/2)*(n:ℝ)^3) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (2*K/a))] with n hn
  have hn' := (div_le_iff₀ ha).mp hn
  have hK : K ≤ a/2*(n:ℝ) := by nlinarith
  have h := mul_le_mul_of_nonneg_right hK (sq_nonneg (n:ℝ))
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith

/-- Any actual finite unitary family of exp(K n²) size inherits a cubic tail, uniformly in that family. -/
theorem quditQuartic_eventually_finite_family_cubic {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) (K : ℝ) :
    ∀ᶠ n : Nat in atTop,
      ∀ S : Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ),
      (∀ U ∈ S, U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) →
      (S.card:ℝ) ≤ Real.exp (K*(n:ℝ)^2) →
      (pairedGaussian (QuditIndex d n))
        {x | ∃ U ∈ S, kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ U x|} ≤
      ENNReal.ofReal (Real.exp (-(Real.log d / 8) * (n:ℝ)^3)) := by
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  have ha : 0 < Real.log d / 4 := div_pos (Real.log_pos hdR) (by norm_num)
  filter_upwards [quditQuartic_eventually_finite_union hd J θ hθ,
    eventually_quadratic_exp_mul_cubic ha K] with n hn hbound
  intro S hS hcard
  apply (hn S hS).trans
  apply ENNReal.ofReal_le_ofReal
  have h := (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)).trans hbound
  convert h using 1; congr 1; ring

end CertificationGaussian
