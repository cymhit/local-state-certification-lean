import CertificationGaussian.ReadoutRemainderAsymptotics
import CertificationGaussian.Consumers.ReadoutRemainderTail

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- The original full-Haar remainder has an explicit positive rate depending only on d; the eventual threshold may depend on r and the signed coefficients. -/
theorem actual_haar_remainder_exponential (d r : ℕ) [NeZero d] (hd : 3≤d) (lam : ℕ → ℝ) :
    0< -(Real.log (haarLocalKappa d)/2) ∧ ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
    pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal (Real.exp (-(-(Real.log (haarLocalKappa d)/2))*(n:ℝ))) := by
  refine ⟨by have h := Real.log_neg (haarLocalKappa_pos d (by omega)) (haarLocalKappa_lt_one d hd); linarith,?_⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp (cardinalityHaar_remainder_eventually_exponential d r hd lam)
  refine ⟨max N 1,le_max_right _ _,fun n hn => ?_⟩
  simpa only [neg_neg] using hN n ((le_max_left _ _).trans hn)

/-- The finite three-Pauli ensemble has one explicit positive exponential rate for every fixed r and coefficient sequence. -/
theorem actual_pauli_remainder_exponential (r : ℕ) (lam : ℕ → ℝ) :
    0< -(Real.log pauliLocalKappa/2) ∧ ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
    pairedGaussian (QuditIndex 2 n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal (Real.exp (-(-(Real.log pauliLocalKappa/2))*(n:ℝ))) := by
  refine ⟨by have h := Real.log_neg pauliLocalKappa_pos pauliLocalKappa_lt_one; linarith,?_⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp (cardinalityPauli_remainder_eventually_exponential r lam)
  refine ⟨max N 1,le_max_right _ _,fun n hn => ?_⟩
  simpa only [neg_neg] using hN n ((le_max_left _ _).trans hn)

/-- The same signed (1,-2,0,...) paper coefficients satisfy the actual exponential operator-event theorem. -/
theorem actual_signed_remainder_eventually :
    ∀ᶠ n : ℕ in atTop,
    pairedGaussian (QuditIndex 2 n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord 2
        signedPaperCoefficients (complexCoordinate x))‖} ≤
      ENNReal.ofReal (Real.exp ((Real.log pauliLocalKappa/2)*n)) :=
  cardinalityPauli_remainder_eventually_exponential 2 signedPaperCoefficients

/-- Terms with degree j>n really vanish in the original Lambda; no n>=r assumption is inserted. -/
theorem actual_lambda_beyond_dimension :
    complementLambda 3 1 3 (fun j => if j=3 then (7:ℝ) else 0)=0 := by
  norm_num [complementLambda,Fin.sum_univ_succ,Nat.choose_eq_zero_of_lt (show 1<3 by decide)]

/-- The constant shell and zero coefficients retain the expected exact polynomial bounds. -/
theorem actual_lambda_constant_and_zero (d n r : ℕ) (a : ℝ) :
    complementLambda d n 0 (fun _ => a)=|a| ∧
    complementLambdaCoefficient d r (fun _ => 0)=0 := by
  simp [complementLambda,complementLambdaCoefficient]

end CertificationGaussian.Consumers
