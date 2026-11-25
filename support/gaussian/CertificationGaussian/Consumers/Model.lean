import CertificationGaussian.Model

noncomputable section
open MeasureTheory GaussianHilbert MvPolynomial
namespace CertificationGaussian.Consumer

theorem polynomial_representation (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :
    ∃ P : MvPolynomial (Fin (2*d^n)) ℝ, P.totalDegree ≤ 4 ∧
      (∀ x, eval x P = quditStandardQuartic d n J θ U x) ∧
      Measurable (quditStandardQuartic d n J θ U) :=
  ⟨quditPolynomial d n J θ U, degree_quditPolynomial d n J θ U,
    eval_quditPolynomial d n J θ U, quditStandardQuartic_measurable d n J θ U⟩

theorem zero_sites_transport : MeasurePreserving (quditCoordinates 2 0)
    (stdGaussianFin 2) (pairedGaussian (QuditIndex 2 0)) := by
  simpa using qudit_coordinate_preserving 2 0

theorem signed_qutrit_example (U : Matrix (QuditIndex 3 2) (QuditIndex 3 2) ℂ) :
    ∃ P : MvPolynomial (Fin 18) ℝ, P.totalDegree ≤ 4 ∧
      ∀ x, eval x P = quditStandardQuartic 3 2 {1,2} (fun k => if k = 1 then -1 else 2) U x := by
  obtain ⟨P,hdegree,heval,_⟩ := polynomial_representation 3 2 {1,2}
    (fun k => if k = 1 then -1 else 2) U
  exact ⟨P,hdegree,heval⟩

end CertificationGaussian.Consumer
