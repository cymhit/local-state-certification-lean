import CertificationGaussian.GaussianVariance
import CertificationGaussian.Moments
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CertificationGaussian

/-- Exact L2 integral identity, using the actual AE Lp representative. -/
theorem eLpNorm_two_toReal_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal^2 = ∫ x, (f x)^2 ∂μ := by
  rw [← Lp.norm_toLp f hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The variance estimate bounds the Gaussian L² norm of the signed Hamming quartic. -/
theorem quditQuartic_eLpNorm_two_le {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) :
    eLpNorm (quditQuartic d n J θ U) 2 (pairedGaussian (QuditIndex d n)) ≤
      ENNReal.ofReal (Real.sqrt (8 * (kernelWeightL1 J θ)^2 * kernelVarianceScale d n J θ / (d^n : ℝ))) := by
  have hf : MemLp (quditQuartic d n J θ U) 2 (pairedGaussian (QuditIndex d n)) := by
    simpa only [quditQuartic, ENNReal.ofReal_ofNat] using gaussianQuartic_memLp U (signedHammingKernel d n J θ) (kernelVarianceScale d n J θ) 2 (by norm_num)
  apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).mp
  rw [eLpNorm_two_toReal_sq hf, Real.sq_sqrt]
  · exact quditQuartic_second_moment_le hd J hJ θ U hU
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (kernelVarianceScale_nonneg d n J θ)) (by positivity)

/-- An explicit fixed-basis Lp bound for the quartic. -/
theorem quditQuartic_eLpNorm_explicit {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (quditQuartic d n J θ U) (ENNReal.ofReal p) (pairedGaussian (QuditIndex d n)) ≤
      ENNReal.ofReal (5*(p-1)^2 * Real.sqrt
        (8 * (kernelWeightL1 J θ)^2 * kernelVarianceScale d n J θ / (d^n : ℝ))) := by
  calc
    _ ≤ ENNReal.ofReal (5*(p-1)^2) *
        eLpNorm (quditQuartic d n J θ U) 2 (pairedGaussian (QuditIndex d n)) :=
      quditQuartic_eLpNorm d n J θ U p hp
    _ ≤ ENNReal.ofReal (5*(p-1)^2) * ENNReal.ofReal (Real.sqrt
        (8 * (kernelWeightL1 J θ)^2 * kernelVarianceScale d n J θ / (d^n : ℝ))) := by
      gcongr
      exact quditQuartic_eLpNorm_two_le hd J hJ θ U hU
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- Markov in the exact real absolute-value event, for any real positive exponent. -/
theorem measure_abs_ge_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) {p C t : ℝ} (hp : 0 < p) (hC : 0 ≤ C) (ht : 0 < t)
    (hLp : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    μ {x | t ≤ |f x|} ≤ ENNReal.ofReal ((C/t)^p) := by
  have h := meas_ge_le_mul_pow_eLpNorm_enorm μ (p := ENNReal.ofReal p) (f := f)
    (by positivity) ENNReal.ofReal_ne_top (ε := ENNReal.ofReal t) (by positivity)
    (by intro h; exact (ENNReal.ofReal_ne_top h).elim)
  rw [ENNReal.toReal_ofReal hp.le] at h
  have he : {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} = {x | t ≤ |f x|} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  rw [he] at h
  calc
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ p * eLpNorm f (ENNReal.ofReal p) μ ^ p := h
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ p * (ENNReal.ofReal C)^p := by gcongr
    _ = (ENNReal.ofReal (C/t))^p := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_div_of_pos ht,
        div_eq_mul_inv, mul_comm]
    _ = _ := ENNReal.ofReal_rpow_of_nonneg (div_nonneg hC ht.le) hp.le

/-- Actual fixed-basis polynomial tail with all dimension and kernel dependence explicit. -/
theorem quditQuartic_abs_tail {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht : 0 < t) :
    (pairedGaussian (QuditIndex d n)) {x | t ≤ |quditQuartic d n J θ U x|} ≤
      ENNReal.ofReal ((5*(p-1)^2 * Real.sqrt
        (8 * (kernelWeightL1 J θ)^2 * kernelVarianceScale d n J θ / (d^n : ℝ)) / t)^p) := by
  exact measure_abs_ge_le_of_eLpNorm_le _ _ (by linarith) (by positivity) ht
    (quditQuartic_eLpNorm_explicit hd J hJ θ U hU p hp)

end CertificationGaussian
