import CertificationGaussian.CardinalityComplementRemainder

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- The actual n-qudit Haar remainder, with the paper's cardinality kernel and Lambda_n, is Hermitian and satisfies up:remainder. -/
theorem paper_haar_remainder (d n r : ℕ) [NeZero d] (hd : 3≤d) (lam : ℕ → ℝ) :
    (∀ z : QuditIndex d n → ℂ,
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam z).IsHermitian) ∧
    (∫ z,(Matrix.trace ((cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam
      (complexCoordinate z))^4)).re ∂pairedGaussian (QuditIndex d n)) ≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (complementLambda d n r lam)^8*(haarLocalKappa d)^(n-8*r) :=
  ⟨fun z => cardinalityReadoutRemainder_isHermitian d (haarBasisRecords d) id continuous_id r lam z,
    by simpa only [Fintype.card_fin] using cardinalityHaar_remainder_bound (S:=Fin n) d hd r lam⟩

/-- The qubit statement uses the original finite three-basis/six-record ensemble, with its proved strict κ. -/
theorem paper_pauli_remainder (n r : ℕ) (lam : ℕ → ℝ) :
    (∀ z : QuditIndex 2 n → ℂ,
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam z).IsHermitian) ∧
    (∫ z,(Matrix.trace ((cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam
      (complexCoordinate z))^4)).re ∂pairedGaussian (QuditIndex 2 n)) ≤
      (Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)*(complementLambda 2 n r lam)^8*pauliLocalKappa^(n-8*r) :=
  ⟨fun z => cardinalityReadoutRemainder_isHermitian 2 pauliBasisRecords pauliFullRecord
    continuous_of_discreteTopology r lam z,
    by simpa only [Fintype.card_fin] using cardinalityPauli_remainder_bound (S:=Fin n) r lam⟩

/-- The actual fourth trace is real and nonnegative pointwise, rather than only bounded after taking real parts. -/
theorem paper_pauli_fourth_trace_real_nonneg (n r : ℕ) (lam : ℕ → ℝ) (z : QuditIndex 2 n → ℂ) :
    (Matrix.trace ((cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam z)^4)).im=0 ∧
      0≤(Matrix.trace ((cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam z)^4)).re := by
  have h := cardinalityReadoutRemainder_isHermitian 2 pauliBasisRecords pauliFullRecord
    continuous_of_discreteTopology r lam z
  exact ⟨hermitian_trace_fourth_im_zero _ h,hermitian_trace_fourth_nonneg _ h⟩

/-- The actual signed paper coefficients include a zero high-order coefficient and the required lambda_0=1. -/
def signedPaperCoefficients (j : ℕ) : ℝ := if j=0 then 1 else if j=1 then -2 else 0

theorem signedPaperCoefficients_lambda : complementLambda 2 16 2 signedPaperCoefficients=33 := by
  norm_num [complementLambda,signedPaperCoefficients,Fin.sum_univ_succ]

theorem actual_signed_paper_remainder :
    (∫ z,(Matrix.trace ((cardinalityReadoutRemainder (S:=Fin 16) 2 pauliBasisRecords pauliFullRecord 2
      signedPaperCoefficients (complexCoordinate z))^4)).re ∂pairedGaussian (QuditIndex 2 16)) ≤
      (Nat.factorial 8:ℝ)*(16:ℝ)^16*33^8 := by
  have h := cardinalityPauli_remainder_bound (S:=Fin 16) 2 signedPaperCoefficients
  simpa only [Fintype.card_fin,signedPaperCoefficients_lambda,show 8*2=16 by decide,
    Nat.sub_self,pow_zero,mul_one] using h

/-- Zero coefficients give the zero actual Bochner matrix, for every z, with no undefined-integral argument. -/
theorem actual_zero_remainder (n r : ℕ) (z : QuditIndex 2 n → ℂ) :
    cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r (fun _ => 0) z=0 := by
  simp [cardinalityReadoutRemainder,finiteComplementRemainder,normalReadoutRemainder,
    finiteComplementKernel,cardinalityComplementWeight,complexGaussianNormalMatrix,sphereQuadraticForm]

/-- n=r=0 is the genuine one-complex-coordinate remainder, not an incorrectly empty Gaussian space. -/
theorem actual_empty_site_remainder_bound :
    (∫ z,(Matrix.trace ((cardinalityReadoutRemainder (S:=Fin 0) 3 (haarBasisRecords 3) id 0
      (fun _ => 1) (complexCoordinate z))^4)).re ∂pairedGaussian (QuditIndex 3 0)) ≤(Nat.factorial 8:ℝ) := by
  have h := cardinalityHaar_remainder_bound (S:=Fin 0) 3 (by decide) 0 (fun _ => 1)
  simpa [complementLambda] using h

end CertificationGaussian.Consumers
