import GaussianHilbert.OUEigenfunctions
import MarkovSemigroups.Instances.WorkInProgress.EuclideanHypercontractive

/-!
# Gaussian log-Sobolev inequalities and spectral OU hypercontractivity

The Gaussian Bakry–Émery structures supply the log-Sobolev inequalities.
For hypercontractivity, the concrete Mehler semigroup already has the required
estimate. We identify its continuous linear operator with the spectral OU
operator by equality of their almost-everywhere representatives, and transport
that estimate along the operator equality.

This local Apache-2.0 implementation uses the public Gaussian interface and
the imported foundations. See `docs/gaussian-bridge.md` for its provenance.
-/

open MeasureTheory MarkovSemigroup

namespace GaussianHilbert

/-- The one-dimensional Gaussian Bakry–Émery structure satisfies its
log-Sobolev inequality. -/
theorem oneDimGaussianLSI : DirichletSpace.SatisfiesLogSobolev
    (ds := Gaussian1D.bakryEmerySpace.toDirichletSpace)
    Gaussian1D.bakryEmerySpace.ρ :=
  BakryEmerySpace.satisfiesLogSobolev (be := Gaussian1D.bakryEmerySpace)

/-- The product Gaussian Bakry–Émery structure satisfies its log-Sobolev
inequality in every finite dimension. -/
theorem stdGaussianFin_LSI (n : ℕ) : DirichletSpace.SatisfiesLogSobolev
    (ds := (stdGaussianFin.bakryEmerySpace n).toDirichletSpace)
    (stdGaussianFin.bakryEmerySpace n).ρ :=
  BakryEmerySpace.satisfiesLogSobolev (be := stdGaussianFin.bakryEmerySpace n)

/-- Log-Sobolev constant `1` for the concrete Gaussian Dirichlet-Markov
semigroup. -/
theorem stdGaussianFin_dirichletMarkovSemigroup_satisfiesLogSobolev (n : ℕ) :
    DirichletMarkovSemigroup.SatisfiesLogSobolev
      (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n) 1 :=
  GaussianFin.stdGaussianFin_satisfiesLogSobolev n

/-- Hypercontractivity at rate `1` for the concrete Gaussian OU semigroup. -/
theorem stdGaussianFin_dirichletMarkovSemigroup_isHypercontractive (n : ℕ) :
    MarkovSemigroup.IsHypercontractive
      (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup 1 :=
  GaussianFin.stdGaussianFin_isHypercontractive n

private theorem spectralOU_eq_concreteOU (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ouSemigroupAct n t = GaussianFin.ouSemigroupFinLp (n := n) t := by
  rw [← mehlerOp_eq_ouSemigroupAct n t ht]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext_iff.mpr
  exact (mehlerOp_apply n t ht f).trans
    (GaussianFin.ouSemigroupFinLp_coeFn_ae t ht f).symm

/-- Nelson's `L² → Lᵖ` estimate for the spectral Gaussian OU action.

For positive time this is the concrete semigroup's hypercontractivity theorem
transported across equality of operators. At time zero, the exponent constraint
forces `p = 2` and the concrete operator is the identity. -/
theorem ouSemigroupAct_eLpNorm_hypercontractive {n : ℕ}
    (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht : 0 ≤ t)
    (h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal p) (stdGaussianFin n) ≤
      eLpNorm ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
  rw [spectralOU_eq_concreteOU n t ht]
  by_cases hzero : t = 0
  · subst t
    have hexponent : p = 2 := by
      norm_num at h_nelson
      linarith
    subst p
    rw [GaussianFin.ouSemigroupFinLp_zero]
    norm_num only [ENNReal.ofReal_ofNat]
    exact le_rfl
  · have hpositive : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have hsource : MemLp (f : (Fin n → ℝ) → ℝ)
        (ENNReal.ofReal (2 : ℝ)) (stdGaussianFin n) := by
      simpa using Lp.memLp f
    have hbound : p ≤ 1 + (2 - 1) * Real.exp (2 * 1 * t) := by
      calc
        p ≤ 1 + Real.exp (2 * t) := by linarith
        _ = 1 + (2 - 1) * Real.exp (2 * 1 * t) := by norm_num
    have hestimate :=
      (GaussianFin.stdGaussianFin_isHypercontractive n).2
        2 p t (by norm_num) hp hpositive hbound f hsource
    norm_num only [ENNReal.ofReal_ofNat] at hestimate
    with_unfolding_all exact hestimate

end GaussianHilbert
