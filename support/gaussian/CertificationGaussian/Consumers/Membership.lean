import CertificationGaussian.Model
import CertificationGaussian.PolynomialMembership

noncomputable section
open MeasureTheory GaussianHilbert
namespace CertificationGaussian.Consumer

theorem qudit_polynomial_chaos (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :
    polynomialLp (quditPolynomial d n J θ U) ∈ wienerChaosLE (2*d^n) 4 :=
  polynomialLp_mem_chaosLE _ (degree_quditPolynomial d n J θ U)

theorem qudit_memLp_two (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :
    MemLp (quditStandardQuartic d n J θ U) 2 (stdGaussianFin (2*d^n)) := by
  simpa only [eval_quditPolynomial] using eval_memLp_two (quditPolynomial d n J θ U)

theorem qudit_Lp_ae (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :
    (polynomialLp (quditPolynomial d n J θ U) : (Fin (2*d^n) → ℝ) → ℝ)
      =ᵐ[stdGaussianFin (2*d^n)] quditStandardQuartic d n J θ U := by
  simpa only [eval_quditPolynomial] using polynomialLp_ae (quditPolynomial d n J θ U)

end CertificationGaussian.Consumer
