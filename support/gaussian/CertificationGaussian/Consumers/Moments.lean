import CertificationGaussian.Moments
import CertificationGaussian.Consumers.Membership

noncomputable section
open MeasureTheory GaussianHilbert
namespace CertificationGaussian.Consumer

theorem mixed_quartic_memLp (p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun x : Fin 2 → ℝ => x 0 ^ 2 * x 1 ^ 2) (ENNReal.ofReal p) (stdGaussianFin 2) := by
  let P : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2
  have hP : P.totalDegree ≤ 4 := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have h0 := MvPolynomial.totalDegree_pow (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) 2
    have h1 := MvPolynomial.totalDegree_pow (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ) 2
    simp only [MvPolynomial.totalDegree_X] at h0 h1
    omega
  simpa [P] using quartic_memLp P hP p hp


theorem zero_moment (m : Nat) (p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun x : Fin m → ℝ => MvPolynomial.eval x (0 : MvPolynomial (Fin m) ℝ))
      (ENNReal.ofReal p) (stdGaussianFin m) :=
  quartic_memLp _ (by simp) p hp

theorem constant_moment (m : Nat) (c p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun x : Fin m → ℝ => MvPolynomial.eval x (MvPolynomial.C c))
      (ENNReal.ofReal p) (stdGaussianFin m) :=
  quartic_memLp _ (by simp) p hp

theorem empty_dimension_moment (c p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun x : Fin 0 → ℝ => MvPolynomial.eval x (MvPolynomial.C c))
      (ENNReal.ofReal p) (stdGaussianFin 0) ≤ ENNReal.ofReal (5*(p-1)^2) *
        eLpNorm (fun x : Fin 0 → ℝ => MvPolynomial.eval x (MvPolynomial.C c)) 2 (stdGaussianFin 0) :=
  quartic_eLpNorm _ (by simp) p hp

/-- Arbitrary dimension, signed coefficients, complex basis matrix, and real p ≥ 2.
The same underlying qudit model and degree proof are imported from Model. -/
theorem qudit_moment (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) (p : ℝ) (hp : 2 ≤ p) :
    MemLp (quditStandardQuartic d n J θ U) (ENNReal.ofReal p) (stdGaussianFin (2*d^n)) ∧
    eLpNorm (quditStandardQuartic d n J θ U) (ENNReal.ofReal p) (stdGaussianFin (2*d^n)) ≤
      ENNReal.ofReal (5*(p-1)^2) * eLpNorm (quditStandardQuartic d n J θ U) 2 (stdGaussianFin (2*d^n)) :=
  ⟨quditStandardQuartic_memLp d n J θ U p hp, quditStandardQuartic_eLpNorm d n J θ U p hp⟩

end CertificationGaussian.Consumer
