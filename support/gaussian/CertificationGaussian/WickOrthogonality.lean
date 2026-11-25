/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license; see licenses/GaussianField-LICENSE.
Extracted from gaussian-field dc2b3b8378b2b7e33eaa8b61d6e943de11ff3f33.
The proofs below are retained; general field/nuclear/lattice infrastructure is excluded.
The extraction selects the Hermite and Wick results needed by this Gaussian support library.
-/
import CertificationGaussian.WickAlgebra
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
noncomputable section
namespace GaussianField
theorem wickMonomial_inner_gaussianReal_one (m n : ℕ) :
    ∫ x : ℝ, wickMonomial m 1 x * wickMonomial n 1 x ∂(gaussianReal 0 1) =
    if m = n then (m.factorial : ℝ) else 0 := by
  -- Step 1: wickMonomial k 1 x = (hermiteR k).eval x.
  have h_wick : ∀ (k : ℕ) (x : ℝ),
      wickMonomial k 1 x = (hermiteR k).eval x := by
    intro k x
    rw [wick_eq_hermiteR k 1 (by norm_num : (0:ℝ) < 1)]
    show Real.sqrt 1 ^ k * (hermiteR k).eval (x / Real.sqrt 1) = _
    rw [Real.sqrt_one, one_pow, one_mul, div_one]
  simp_rw [h_wick]
  -- Step 2: Convert gaussianReal 0 1 integral to Lebesgue with the PDF.
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  simp_rw [smul_eq_mul]
  -- Step 3: Identify gaussianPDFReal 0 1 x = (√(2π))⁻¹ * gaussian x.
  have h_pdf : ∀ x : ℝ,
      gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * gaussian x := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x^2 / 2) =
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x^2 / 2))
    congr 2
    ring
  simp_rw [h_pdf]
  -- Step 4: Pull out the (√(2π))⁻¹ constant; what's left is `J m n`.
  rw [show (fun x : ℝ =>
        (Real.sqrt (2 * Real.pi))⁻¹ * gaussian x *
          ((hermiteR m).eval x * (hermiteR n).eval x)) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        ((hermiteR m).eval x * ((hermiteR n).eval x * gaussian x))) from by
    funext x; ring]
  rw [integral_const_mul]
  show (Real.sqrt (2 * Real.pi))⁻¹ * J m n = _
  rw [J_eq n m]
  -- Goal: (√(2π))⁻¹ * (if m = n then m! * √(2π) else 0) = if m = n then m! else 0
  split_ifs with h
  · have h2pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) :=
      Real.sqrt_pos.mpr (by positivity)
    field_simp
  · ring


end GaussianField
