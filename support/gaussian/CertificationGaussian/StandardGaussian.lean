/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.
The following definition is extracted unchanged from GaussianHilbert/HermitePolynomials.lean
in gaussian-hilbert at commit 4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace GaussianHilbert
/-- Product of n independent standard real Gaussian measures. -/
def stdGaussianFin (n : ℕ) : MeasureTheory.Measure (Fin n → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
end GaussianHilbert
