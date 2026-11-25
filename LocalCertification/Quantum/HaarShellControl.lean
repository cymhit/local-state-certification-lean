import LocalCertification.Quantum.HaarWeylOverlap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open scoped BigOperators ENNReal
open MeasureTheory Metric Set
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

/-- A real nonnegative Markov bound, directly from the actual Bochner expectation. -/
theorem nonnegative_markov_lt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℝ} (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x)
    {t : ℝ} (ht : 0 < t) :
    μ {x | t < f x} ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / t) := by
  calc
    μ {x | t < f x} ≤ μ {x | ENNReal.ofReal t ≤ ENNReal.ofReal (f x)} :=
      measure_mono (fun x hx => ENNReal.ofReal_le_ofReal (le_of_lt hx))
    _ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / ENNReal.ofReal t :=
      meas_ge_le_lintegral_div hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hn),
        ← ENNReal.ofReal_div_of_pos ht]

variable {d : ℕ} [NeZero d] {n : ℕ}

/-- A positive cutoff is arbitrary, so this applies to polynomial and exponential leakage scales. -/
theorem haar_shell_failure (hd : 2 ≤ d) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    {t : ℝ} (ht : 0 < t) :
    CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
      {U | t < pureTargetFidelity (haarPureVector ψ U)
        (pureTargetShell hd (haarPureVector ψ U) j hj)} ≤
      ENNReal.ofReal (1 / (t * ((d : ℝ)^n + 1))) := by
  have h := nonnegative_markov_lt _ (haar_pureTargetShell_fidelity_integrable hd j hj ψ)
    (fun U => pureTargetShell_fidelity_nonneg hd (haarPureVector ψ U) j hj) ht
  rw [haar_pureTargetShell_fidelity hd hj0 hj ψ] at h
  simpa [div_eq_mul_inv, mul_comm] using h

/-- Simultaneous control of any finite collection of actual physical nonzero shells. -/
theorem haar_shell_failure_finset (hd : 2 ≤ d) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j ∧ j ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    {t : ℝ} (ht : 0 < t) :
    CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
      {U | ∃ j : J, t < pureTargetFidelity (haarPureVector ψ U)
        (pureTargetShell hd (haarPureVector ψ U) j.val (hJ j.val j.property).2)} ≤
      ENNReal.ofReal ((J.card : ℝ) / (t * ((d : ℝ)^n + 1))) := by
  classical
  rw [Set.ofPred_exists]
  calc
    _ ≤ ∑ j : J, CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
        {U | t < pureTargetFidelity (haarPureVector ψ U)
          (pureTargetShell hd (haarPureVector ψ U) j.val (hJ j.val j.property).2)} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : J, ENNReal.ofReal (1 / (t * ((d : ℝ)^n + 1))) := by
      apply Finset.sum_le_sum
      intro j _
      exact haar_shell_failure hd (hJ j.val j.property).1 (hJ j.val j.property).2 ψ ht
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

/-- The probability estimate supplies a common target whenever its explicit failure bound is below one. -/
theorem exists_haar_shell_control (hd : 2 ≤ d) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 0 < j ∧ j ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    {t : ℝ} (ht : 0 < t) (hsmall : (J.card : ℝ) / (t * ((d : ℝ)^n + 1)) < 1) :
    ∃ U : CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n), ∀ j : J,
      pureTargetFidelity (haarPureVector ψ U)
        (pureTargetShell hd (haarPureVector ψ U) j.val (hJ j.val j.property).2) ≤ t := by
  by_contra h
  push Not at h
  have hb := haar_shell_failure_finset hd J hJ ψ ht
  have he : {U | ∃ j : J, t < pureTargetFidelity (haarPureVector ψ U)
      (pureTargetShell hd (haarPureVector ψ U) j.val (hJ j.val j.property).2)} = Set.univ :=
    Set.eq_univ_of_forall h
  rw [he, measure_univ] at hb
  exact (not_lt_of_ge hb) (ENNReal.ofReal_lt_one.mpr hsmall)

end LocalCertification.Quantum
