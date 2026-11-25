import LocalCertification.Certificates.DimensionValues
import LocalCertification.Certificates.StagedSearch

/-! # Blaschke estimates and certificates in the dimension parameter

The analytic bounds use a positive real parameter. The exact search uses a
positive rational parameter so that its certificate checks use rational arithmetic.
-/

set_option autoImplicit false
open Polynomial LocalCertification.Asymptotic
open LocalCertification.Certificates

namespace LocalCertification.Manuscript

theorem blaschke_coefficient_lower (d : ℝ) (hd : 0 < d) (r : ℕ) :
    2 * (d + 1)⁻¹ ^ (r + 1) /
      (1 + ∑' n, |blaschkeCoeff (d + 1)⁻¹ (r + 1) n|) ≤ gamma d r :=
  EulerMoments.gamma_blaschke_coefficient_lower (d + 1) (by linarith) r

theorem blaschke_lower (d : ℝ) (hd : 0 < d) (r : ℕ) :
    2 * (d + 1)⁻¹ ^ (r + 1) /
      (1 + blaschkeCoefficientConstant (d + 1) * Real.sqrt (r + 1)) ≤ gamma d r :=
  EulerMoments.gamma_blaschke_lower (d + 1) (by linarith) r

/-- A positive rational dimension supplies a geometric base greater than one. -/
theorem certificate_base_gt_one {d : ℚ} (hd : 0 < d) : 1 < ((d + 1 : ℚ) : ℝ) := by
  exact_mod_cast (show (1 : ℚ) < d + 1 by linarith)

theorem certificate_optimality (d : ℚ) (hd : 0 < d) (r : ℕ)
    (c : CanonicalCandidate (d + 1) r) (M : ℕ) (hc : c.canonicalCheck M) :
    (c.beta : ℝ) = Extremal.extremalValue ((d : ℝ) + 1) r ∧
    gamma d r = ((2 / (1 + c.beta) : ℚ) : ℝ) ∧
    Extremal.admissible r (c.p.map (Rat.castHom ℝ)) ∧
    Extremal.envelopeRatio ((d : ℝ) + 1) (c.p.map (Rat.castHom ℝ)) = gamma d r ∧
    ∀ P : ℝ[X], Extremal.admissible r P →
      Extremal.envelopeRatio ((d : ℝ) + 1) P = gamma d r → P = c.p.map (Rat.castHom ℝ) := by
  simpa only [gamma, Rat.cast_add, Rat.cast_one] using
    c.optimality (certificate_base_gt_one hd) M hc

theorem certificate_exists (d : ℚ) (hd : 0 < d) (r : ℕ) :
    ∃ (c : CanonicalCandidate (d + 1) r) (M : ℕ), c.canonicalCheck M ∧
      Extremal.admissible r (c.p.map (Rat.castHom ℝ)) ∧
      Extremal.envelopeRatio ((d : ℝ) + 1) (c.p.map (Rat.castHom ℝ)) = gamma d r := by
  obtain ⟨c, M, hc⟩ := canonical_certificate_exists (d + 1) (certificate_base_gt_one hd) r
  obtain ⟨_, _, hdeg, hval, _⟩ := certificate_optimality d hd r c M hc
  exact ⟨c, M, hc, hdeg, hval⟩

theorem certificate_search_terminates (d : ℚ) (hd : 0 < d) (r : ℕ) :
    stagedFind (d + 1) r (stagedSearchIndex (d + 1) (certificate_base_gt_one hd) r) =
      some (stagedSearch (d + 1) (certificate_base_gt_one hd) r) :=
  stagedSearch_terminates (d + 1) (certificate_base_gt_one hd) r

/-- The search returns a passing certificate, its exact value and its unique optimizer. -/
theorem certificate_output_correct (d : ℚ) (hd : 0 < d) (r : ℕ) :
    let h := certificate_base_gt_one hd
    let p := (Polynomial.ofFn (r + 1) (stagedPolynomial (d + 1) h r)).map (Rat.castHom ℝ)
    canonicalRawCheck (d + 1) r (stagedSearch (d + 1) h r) = true ∧
    (stagedGamma (d + 1) h r : ℝ) = gamma d r ∧
    Extremal.admissible r p ∧ Extremal.envelopeRatio ((d : ℝ) + 1) p = gamma d r ∧
    ∀ P : ℝ[X], Extremal.admissible r P →
      Extremal.envelopeRatio ((d : ℝ) + 1) P = gamma d r → P = p := by
  refine ⟨stagedSearch_passes (d + 1) (certificate_base_gt_one hd) r, ?_⟩
  simpa only [gamma, Rat.cast_add, Rat.cast_one] using
    stagedOutput_correct (d + 1) (certificate_base_gt_one hd) r

theorem low_degree_values :
    (∀ d : ℝ, 0 < d → gamma d 0 = 1 / (d + 1)) ∧
    (∀ d : ℝ, 1 ≤ d → gamma d 1 = 1 / ((d + 1) ^ 2 + 1)) ∧
    (∀ d : ℝ, 3 ≤ d → gamma d 2 = 1 / ((d + 1) * ((d + 1) ^ 2 + 3))) ∧
    gamma 2 2 = 1 / 35 :=
  ⟨fun d hd => by simpa only [one_div] using gamma_zero d hd,
    gamma_one, gamma_two, qubit_quadratic_exact⟩

end LocalCertification.Manuscript
