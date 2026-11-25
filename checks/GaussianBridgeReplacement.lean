import GaussianHilbert.HypercontractivityFromBE
import Lean

/-! Independent interface targets for the Gaussian hypercontractivity bridge.
The targets specify the Gaussian log-Sobolev and Nelson inequalities. -/

open MeasureTheory MarkovSemigroup GaussianHilbert

example : DirichletSpace.SatisfiesLogSobolev
    (ds := Gaussian1D.bakryEmerySpace.toDirichletSpace)
    Gaussian1D.bakryEmerySpace.ρ := oneDimGaussianLSI

example (n : ℕ) : DirichletSpace.SatisfiesLogSobolev
    (ds := (stdGaussianFin.bakryEmerySpace n).toDirichletSpace)
    (stdGaussianFin.bakryEmerySpace n).ρ := stdGaussianFin_LSI n

example (n : ℕ) : DirichletMarkovSemigroup.SatisfiesLogSobolev
    (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n) 1 :=
  stdGaussianFin_dirichletMarkovSemigroup_satisfiesLogSobolev n

example (n : ℕ) : MarkovSemigroup.IsHypercontractive
    (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup 1 :=
  stdGaussianFin_dirichletMarkovSemigroup_isHypercontractive n

example {n : ℕ} (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht : 0 ≤ t)
    (h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal p) (stdGaussianFin n) ≤
      eLpNorm ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) :=
  ouSemigroupAct_eLpNorm_hypercontractive p hp t ht h_nelson f

example {n : ℕ} (f : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm ((ouSemigroupAct n 0 f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) ≤
      eLpNorm ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
  simpa using ouSemigroupAct_eLpNorm_hypercontractive
    (n := n) 2 (by norm_num) 0 (by norm_num) (by norm_num) f

#print axioms GaussianHilbert.oneDimGaussianLSI
#print axioms GaussianHilbert.stdGaussianFin_LSI
#print axioms GaussianHilbert.stdGaussianFin_dirichletMarkovSemigroup_satisfiesLogSobolev
#print axioms GaussianHilbert.stdGaussianFin_dirichletMarkovSemigroup_isHypercontractive
#print axioms GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive
/-! Declaration and transitive-axiom checks for the Gaussian inequalities. -/

open Lean Elab Command

run_elab do
  let env ← getEnv
  let expected : List String := [
    "GaussianHilbert.oneDimGaussianLSI",
    "GaussianHilbert.stdGaussianFin_LSI",
    "GaussianHilbert.stdGaussianFin_dirichletMarkovSemigroup_satisfiesLogSobolev",
    "GaussianHilbert.stdGaussianFin_dirichletMarkovSemigroup_isHypercontractive",
    "GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive",
    "_private.GaussianHilbert.HypercontractivityFromBE.0.GaussianHilbert.spectralOU_eq_concreteOU"]
  let mut selected : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if env.header.moduleNames[idx.toNat]!.toString == "GaussianHilbert.HypercontractivityFromBE" then
      selected := selected.push n
  unless selected.size == expected.length && selected.all (fun n => expected.contains n.toString) do
    throwError "Gaussian bridge declaration identity mismatch: {selected}"
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for n in selected.qsort Name.quickLt do
    let axioms ← collectAxioms n
    let axioms := axioms.qsort Name.quickLt
    unless axioms.all (fun a => allowed.contains a) do
      throwError "Disallowed Gaussian bridge axiom in {n}: {axioms}"
    logInfo m!"GAUSSIAN_BRIDGE_AXIOMS\t{(Json.mkObj [("declaration", toJson n.toString),
      ("axioms", toJson (axioms.map toString))]).compress}"
  logInfo "GAUSSIAN_BRIDGE_AXIOMS_PASS\t6"

#eval IO.println "REGRESSION_CHECK\tGaussianBridgeReplacement\tPASS"
