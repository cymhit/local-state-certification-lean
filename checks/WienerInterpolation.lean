import LocalCertification.Paper
import LocalCertification.Asymptotic.WienerInversion

set_option autoImplicit false
open LocalCertification LocalCertification.Asymptotic.Wiener

example (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (r : ℕ) :
    phi a r ≤ Real.sqrt (Real.exp 1 * (r + 1 : ℕ)) := schaffer_upper a ha ha1 r

example (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, c * Real.sqrt (r + 1 : ℕ) ≤ phi a r :=
  szehr_zarouf_lower a ha ha1

example (q : ℝ) (hq : 1 < q) (r : ℕ) :
    Extremal.extremalValue q r = (q⁻¹ ^ (r+1))⁻¹ *
      sInf (boundaryNorm '' {c | Feasible q⁻¹ r c}) :=
  augmented_complex_infimum q hq r

#check LocalCertification.Asymptotic.blaschke_cauchy_uniform_derivatives
#check LocalCertification.Asymptotic.Wiener.derivatives_iff_polynomial_moments
#check LocalCertification.Asymptotic.Wiener.interpolation_sandwich
#check LocalCertification.Manuscript.wiener_sharp_order_and_inversion
#check LocalCertification.Manuscript.sharp_order_and_inversion

open scoped Topology
open Filter Asymptotics

/-- The printed asymptotics in integer dimension, including the direction of
the gap limit and the sign of the logarithmic correction. -/
private def ManuscriptAsymptotics (d : ℕ) : Prop :=
  (∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ j : ℕ, 2 ≤ j →
    lo * ((d : ℝ)+1)^(-(j : ℝ)) / Real.sqrt j ≤ Manuscript.gamma d j ∧
    Manuscript.gamma d j ≤ hi * ((d : ℝ)+1)^(-(j : ℝ)) / Real.sqrt j) ∧
  (let L := fun g : ℝ => Real.logb ((d : ℝ)+1) (1/g)
   (fun g : ℝ => (Manuscript.criticalDegree d g : ℝ) -
     (L g - (1/2)*Real.logb ((d : ℝ)+1) (L g))) =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)))

example (d : ℕ) (hd : 2 ≤ d) : ManuscriptAsymptotics d := by
  simpa only [ManuscriptAsymptotics, one_div] using Paper.theorem_3 d hd

example (d : ℕ) (hd : 2 ≤ d) : ManuscriptAsymptotics d := by
  simpa only [ManuscriptAsymptotics, one_div] using Paper.theorem_3_wiener d hd

#eval IO.println "WienerInterpolation_PASS"
