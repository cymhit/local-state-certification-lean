import LocalCertification.Extremal.DimensionParameters
import LocalCertification.Extremal.InfinitySupport

/-! # Exact endpoints of the optimal envelope

At an optimum the affine normalization of the actual interval is the
maximizing extrapolant. Its alternating contact at infinity fixes one
endpoint, and the attained ratio determines the other.
-/

set_option autoImplicit false
open Polynomial
namespace LocalCertification.Manuscript

private theorem optimizer_limit_contact (d : ℝ) (hd : 0 < d) (r : ℕ) (p : ℝ[X])
    (hp : Extremal.admissible r p) (hopt : Extremal.envelopeRatio (d + 1) p = gamma d r) :
    -(u d p + ell d p) = (-1 : ℝ) ^ (r + 1) * (u d p - ell d p) := by
  have hq : 1 < d + 1 := by linarith
  have h := Extremal.extremizer_limit_value (d + 1) hq r
    (Extremal.envelopeCandidate (d + 1) r p)
    (Extremal.envelopeCandidate_feasible _ hq r hp)
    (Extremal.envelopeCandidate_maximizes _ hq r hp hopt)
  exact (div_eq_iff (Extremal.envelope_width_pos _ hq hp.2).ne').mp h

/-- The true infimum and supremum of any normalized even-degree optimizer. -/
theorem optimizer_endpoints_even (d : ℝ) (hd : 0 < d) (r : ℕ) (hr : Even r)
    (p : ℝ[X]) (hp : Extremal.admissible r p)
    (hopt : Extremal.envelopeRatio (d + 1) p = gamma d r) :
    (ell d p, u d p) = (0, gamma d r) := by
  have hc := optimizer_limit_contact d hd r p hp hopt
  rw [pow_succ, hr.neg_one_pow] at hc
  have hl : ell d p = 0 := by linarith
  change (u d p - ell d p) / (1 - ell d p) = gamma d r at hopt
  exact Prod.ext hl (by simpa [hl] using hopt)

/-- The true infimum and supremum of any normalized odd-degree optimizer. -/
theorem optimizer_endpoints_odd (d : ℝ) (hd : 0 < d) (r : ℕ) (hr : Odd r)
    (p : ℝ[X]) (hp : Extremal.admissible r p)
    (hopt : Extremal.envelopeRatio (d + 1) p = gamma d r) :
    (ell d p, u d p) = (-gamma d r / (1 - gamma d r), 0) := by
  have hq : 1 < d + 1 := by linarith
  have hc := optimizer_limit_contact d hd r p hp hopt
  rw [pow_succ, hr.neg_one_pow] at hc
  have hu : u d p = 0 := by linarith
  have hg : gamma d r < 1 :=
    (Extremal.gamma_le_inverse _ hq r).trans_lt ((inv_lt_one₀ (by linarith)).mpr hq)
  change (u d p - ell d p) / (1 - ell d p) = gamma d r at hopt
  have h := (div_eq_iff (Extremal.envelope_denominator_pos _ hq p).ne').mp hopt
  change u d p - ell d p = gamma d r * (1 - ell d p) at h
  apply Prod.ext _ hu
  apply (eq_div_iff (sub_pos.mpr hg).ne').mpr
  change ell d p * (1 - gamma d r) = -gamma d r
  nlinarith

end LocalCertification.Manuscript
