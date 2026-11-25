import CertificationGaussian.ReadoutRemainderTail
import CertificationGaussian.Consumers.FiniteComplementRemainder

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- The same actual Haar operator-norm event is both Borel and bounded on the original Gaussian law. -/
theorem actual_haar_remainder_event (d n r : ℕ) [NeZero d] (hd : 3≤d)
    (lam : ℕ → ℝ) (t : ℝ) (ht : 0<t) :
    MeasurableSet {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖} ∧
    pairedGaussian (QuditIndex d n) {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal ((Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (complementLambda d n r lam)^8*(haarLocalKappa d)^(n-8*r)/t^4) :=
  ⟨finiteComplementRemainder_bad_measurable d (haarBasisRecords d) id continuous_id
    (cardinalityComplementSet (S:=Fin n) (r:=r)) (cardinalityComplementWeight lam) t,
    cardinalityHaar_remainder_tail d n r hd lam t ht⟩

/-- The true finite three-Pauli-basis remainder event is also Borel, with no abstract random-matrix surrogate. -/
theorem actual_pauli_remainder_event (n r : ℕ) (lam : ℕ → ℝ) (t : ℝ) (ht : 0<t) :
    MeasurableSet {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖} ∧
    pairedGaussian (QuditIndex 2 n) {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal ((Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)*(complementLambda 2 n r lam)^8*
        pauliLocalKappa^(n-8*r)/t^4) :=
  ⟨finiteComplementRemainder_bad_measurable 2 pauliBasisRecords pauliFullRecord continuous_of_discreteTopology
    (cardinalityComplementSet (S:=Fin n) (r:=r)) (cardinalityComplementWeight lam) t,
    cardinalityPauli_remainder_tail n r lam t ht⟩

/-- The signed paper kernel has the precise n^12 threshold factor on the same measurable event. -/
theorem actual_signed_paper_tail :
    pairedGaussian (QuditIndex 2 16) {x | ((16:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 16) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin 16) 2 pauliBasisRecords pauliFullRecord 2
        signedPaperCoefficients (complexCoordinate x))‖} ≤
      ENNReal.ofReal ((16:ℝ)^12*(Nat.factorial 8:ℝ)*(16:ℝ)^16*33^8) := by
  have h := cardinalityPauli_remainder_tail_n_inv_three 16 2 (by decide) signedPaperCoefficients
  simpa only [Nat.cast_ofNat,signedPaperCoefficients_lambda,show 8*2=16 by decide,Nat.sub_self,pow_zero,mul_one] using h

/-- Zero actual coefficients give a genuinely empty positive-threshold operator event. -/
theorem actual_zero_remainder_event (n r : ℕ) (t : ℝ) (ht : 0<t) :
    pairedGaussian (QuditIndex 2 n) {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r (fun _ => 0)
        (complexCoordinate x))‖}=0 := by
  simp [actual_zero_remainder,not_lt.mpr ht.le]

/-- n=0 uses an arbitrary positive threshold, rather than misusing the n^(-3) positive-threshold theorem. -/
theorem actual_empty_site_positive_threshold (t : ℝ) (ht : 0<t) :
    pairedGaussian (QuditIndex 3 0) {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex 3 0) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin 0) 3 (haarBasisRecords 3) id 0 (fun _ => 1)
        (complexCoordinate x))‖} ≤ ENNReal.ofReal ((Nat.factorial 8:ℝ)/t^4) := by
  have h := cardinalityHaar_remainder_tail 3 0 0 (by decide) (fun _ => 1) t ht
  simpa [complementLambda] using h

end CertificationGaussian.Consumers
