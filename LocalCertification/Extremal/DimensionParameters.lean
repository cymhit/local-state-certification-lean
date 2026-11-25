import LocalCertification.Asymptotic.EulerMomentAsymptotics
import LocalCertification.Extremal.RationalExtremizer

/-! # Dimension, envelopes and strict crossing index

The real parameter `d` is positive. The geometric base in the weighted
polynomial problem is `d + 1`. Physical dimensions enter by the natural cast.
-/

set_option autoImplicit false
open scoped Topology
open Polynomial Filter Asymptotics

noncomputable section
namespace LocalCertification.Manuscript

/-- The weighted value at weight `w`. Only positive weights enter the envelopes. -/
def weightedSample (d : ℝ) (p : ℝ[X]) (w : ℕ) : ℝ :=
  (d + 1)⁻¹ ^ w * p.eval (w : ℝ)

/-- Infimum over all strictly positive integer weights. -/
def ell (d : ℝ) (p : ℝ[X]) : ℝ := Extremal.lowerEnvelope (d + 1) p

/-- Supremum over all strictly positive integer weights. -/
def u (d : ℝ) (p : ℝ[X]) : ℝ := Extremal.upperEnvelope (d + 1) p

/-- The degree-`r` critical value at dimension parameter `d`. -/
def gamma (d : ℝ) (r : ℕ) : ℝ := Extremal.gamma (d + 1) r

/-- Least nonnegative degree at which the critical value is strictly below `g`. -/
def criticalDegree (d g : ℝ) : ℕ := Asymptotic.criticalDegree (d + 1) g

theorem weightedSample_succ (d : ℝ) (p : ℝ[X]) (k : ℕ) :
    weightedSample d p (k + 1) = Extremal.weightedValue (d + 1) p k := rfl

theorem ell_eq_inf (d : ℝ) (p : ℝ[X]) :
    ell d p = sInf (Set.range (fun k : ℕ => weightedSample d p (k + 1))) := rfl

theorem u_eq_sup (d : ℝ) (p : ℝ[X]) :
    u d p = sSup (Set.range (fun k : ℕ => weightedSample d p (k + 1))) := rfl

theorem gamma_eq_inf (d : ℝ) (r : ℕ) :
    gamma d r = sInf ((fun p => (u d p - ell d p) / (1 - ell d p)) ''
      {p : ℝ[X] | Extremal.admissible r p}) := rfl

theorem criticalDegree_eq_min (d g : ℝ) :
    criticalDegree d g = sInf {r : ℕ | gamma d r < g} := rfl

theorem criticalDegree_le_iff (d : ℝ) (hd : 0 < d) (g : ℝ) (hg : 0 < g) (r : ℕ) :
    criticalDegree d g ≤ r ↔ gamma d r < g :=
  Asymptotic.criticalDegree_le_iff (d + 1) (by linarith) g hg r

theorem criticalDegree_at_critical_value (d : ℝ) (hd : 0 < d) (r : ℕ) :
    criticalDegree d (gamma d r) = r + 1 :=
  Asymptotic.criticalDegree_at_critical_value (d + 1) (by linarith) r

theorem gamma_zero (d : ℝ) (hd : 0 < d) : gamma d 0 = (d + 1)⁻¹ :=
  Extremal.gamma_zero (d + 1) (by linarith)

/-- At target fidelity one the normalized gap is one, for any lower threshold below one. -/
theorem criticalDegree_at_unit_fidelity (d : ℝ) (hd : 0 < d) (b : ℝ) (hb : b < 1) :
    criticalDegree d ((1 - b) / (1 - b)) = 0 := by
  rw [div_self (sub_ne_zero.mpr hb.ne')]
  apply Nat.eq_zero_of_le_zero
  rw [criticalDegree_le_iff d hd 1 zero_lt_one 0, gamma_zero d hd]
  exact (inv_lt_one₀ (by linarith : 0 < d + 1)).mpr (by linarith)

theorem gamma_rational (d : ℚ) (hd : 0 < d) (r : ℕ) :
    ∃ v : ℚ, (v : ℝ) = gamma (d : ℝ) r := by
  have hq : 1 < ((d + 1 : ℚ) : ℝ) := by exact_mod_cast (show (1 : ℚ) < d + 1 by linarith)
  simpa only [gamma, Rat.cast_add, Rat.cast_one] using Extremal.gamma_rational (d + 1) hq r

/-- The self-contained Blaschke proof of sharp decay and strict logarithmic inversion. -/
theorem sharp_order_and_inversion (d : ℝ) (hd : 0 < d) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      c * (d + 1) ^ (-(r : ℝ)) / Real.sqrt r ≤ gamma d r ∧
      gamma d r ≤ C * (d + 1) ^ (-(r : ℝ)) / Real.sqrt r) ∧
    ((fun g : ℝ => (criticalDegree d g : ℝ) -
      (Real.logb (d + 1) g⁻¹ - (1 / 2) * Real.logb (d + 1) (Real.logb (d + 1) g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ))) :=
  Asymptotic.EulerMoments.sharp_order_and_inversion (d + 1) (by linarith)

theorem physical_critical_boundary (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    criticalDegree (d : ℝ) (gamma (d : ℝ) r) = r + 1 :=
  criticalDegree_at_critical_value d (by exact_mod_cast (show 0 < d by omega)) r

/-- Sharp step-point decay and strict inversion in integer local dimension,
proved by self-contained coefficient estimates. -/
theorem physical_sharp_order_and_inversion (d : ℕ) (hd : 2 ≤ d) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ j : ℕ, 2 ≤ j →
      c * ((d : ℝ) + 1) ^ (-(j : ℝ)) / Real.sqrt j ≤ gamma d j ∧
      gamma d j ≤ C * ((d : ℝ) + 1) ^ (-(j : ℝ)) / Real.sqrt j) ∧
    ((fun g : ℝ => (criticalDegree d g : ℝ) -
      (Real.logb ((d : ℝ) + 1) g⁻¹ -
        (1 / 2) * Real.logb ((d : ℝ) + 1) (Real.logb ((d : ℝ) + 1) g⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ))) :=
  sharp_order_and_inversion d (by exact_mod_cast (show 0 < d by omega))

end LocalCertification.Manuscript
