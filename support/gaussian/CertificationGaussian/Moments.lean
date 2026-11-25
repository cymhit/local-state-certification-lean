/- Explicit quartic moments over the standard Gaussian model,
using the MemLp conventions of the pinned Lean and mathlib toolchain.
No chaos-membership premise is exposed to consumers. -/
import CertificationGaussian.PolynomialMembership
import CertificationGaussian.Model
import GaussianHilbert.PolynomialChaosConcentration

noncomputable section
open MeasureTheory GaussianHilbert
open scoped BigOperators ENNReal
namespace CertificationGaussian

theorem quartic_eLpNorm {m : Nat} (P : MvPolynomial (Fin m) ℝ) (hP : P.totalDegree ≤ 4)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun x => MvPolynomial.eval x P) (ENNReal.ofReal p) (stdGaussianFin m) ≤
      ENNReal.ofReal (5 * (p-1)^2) * eLpNorm (fun x => MvPolynomial.eval x P) 2 (stdGaussianFin m) := by
  have h := bonami_nelson_chaosLE m 4 (polynomialLp P) (polynomialLp_mem_chaosLE P hP) p hp
  rw [eLpNorm_congr_ae (polynomialLp_ae P), eLpNorm_congr_ae (polynomialLp_ae P)] at h
  convert h using 1
  norm_num

theorem quartic_memLp {m : Nat} (P : MvPolynomial (Fin m) ℝ) (hP : P.totalDegree ≤ 4)
    (p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun x => MvPolynomial.eval x P) (ENNReal.ofReal p) (stdGaussianFin m) := by
  refine lt_of_le_of_lt (quartic_eLpNorm P hP p hp) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (eval_memLp_two P).eLpNorm_lt_top

section Paired
variable (I : Type*) [Fintype I]

theorem paired_quartic_eLpNorm (P : MvPolynomial (Fin 2 × I) ℝ)
    (hP : P.totalDegree ≤ 4) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun x => MvPolynomial.eval x P) (ENNReal.ofReal p) (pairedGaussian I) ≤
      ENNReal.ofReal (5*(p-1)^2) * eLpNorm (fun x => MvPolynomial.eval x P) 2 (pairedGaussian I) := by
  have hd : (flattenPolynomial I P).totalDegree ≤ 4 :=
    (MvPolynomial.totalDegree_rename_le _ P).trans hP
  have h := quartic_eLpNorm (flattenPolynomial I P) hd p hp
  simp only [eval_flatten] at h
  change eLpNorm ((fun x => MvPolynomial.eval x P) ∘ coordEquiv I) _ _ ≤
    _ * eLpNorm ((fun x => MvPolynomial.eval x P) ∘ coordEquiv I) _ _ at h
  rwa [coord_eLpNorm, coord_eLpNorm] at h

theorem paired_quartic_memLp (P : MvPolynomial (Fin 2 × I) ℝ)
    (hP : P.totalDegree ≤ 4) (p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun x => MvPolynomial.eval x P) (ENNReal.ofReal p) (pairedGaussian I) := by
  have hd : (flattenPolynomial I P).totalDegree ≤ 4 :=
    (MvPolynomial.totalDegree_rename_le _ P).trans hP
  have h := quartic_memLp (flattenPolynomial I P) hd p hp
  simp only [eval_flatten] at h
  change eLpNorm _ _ _ < ∞
  rw [← coord_eLpNorm I (fun x => MvPolynomial.eval x P)]
  exact h

end Paired

section Matrix
variable {I : Type*} [Fintype I]

theorem gaussianQuartic_eLpNorm (U : Matrix I I ℂ) (R : Matrix I I ℝ) (v : ℝ) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (gaussianQuartic U R v) (ENNReal.ofReal p) (pairedGaussian I) ≤
      ENNReal.ofReal (5*(p-1)^2) * eLpNorm (gaussianQuartic U R v) 2 (pairedGaussian I) := by
  simpa only [eval_quartic] using paired_quartic_eLpNorm I (quarticPoly U R v) (degree_quartic U R v) p hp

theorem gaussianQuartic_memLp (U : Matrix I I ℂ) (R : Matrix I I ℝ) (v : ℝ) (p : ℝ) (hp : 2 ≤ p) :
    MemLp (gaussianQuartic U R v) (ENNReal.ofReal p) (pairedGaussian I) := by
  simpa only [eval_quartic] using paired_quartic_memLp I (quarticPoly U R v) (degree_quartic U R v) p hp

end Matrix

theorem quditQuartic_eLpNorm (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (quditQuartic d n J θ U) (ENNReal.ofReal p) (pairedGaussian (QuditIndex d n)) ≤
      ENNReal.ofReal (5*(p-1)^2) * eLpNorm (quditQuartic d n J θ U) 2 (pairedGaussian (QuditIndex d n)) :=
  gaussianQuartic_eLpNorm U _ _ p hp

theorem quditStandardQuartic_eLpNorm (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (quditStandardQuartic d n J θ U) (ENNReal.ofReal p) (stdGaussianFin (2*d^n)) ≤
      ENNReal.ofReal (5*(p-1)^2) * eLpNorm (quditStandardQuartic d n J θ U) 2 (stdGaussianFin (2*d^n)) := by
  simpa only [eval_quditPolynomial] using
    quartic_eLpNorm (quditPolynomial d n J θ U) (degree_quditPolynomial d n J θ U) p hp

theorem quditStandardQuartic_memLp (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) (p : ℝ) (hp : 2 ≤ p) :
    MemLp (quditStandardQuartic d n J θ U) (ENNReal.ofReal p) (stdGaussianFin (2*d^n)) := by
  simpa only [eval_quditPolynomial] using
    quartic_memLp (quditPolynomial d n J θ U) (degree_quditPolynomial d n J θ U) p hp


end CertificationGaussian
