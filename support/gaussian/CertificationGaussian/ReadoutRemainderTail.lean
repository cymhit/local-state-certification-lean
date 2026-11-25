import CertificationGaussian.ReadoutRemainderPolynomial
import CertificationGaussian.GaussianMatrixOperatorMoments

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- Markov for the genuine Euclidean operator norm, dominated by the actual Hermitian fourth trace. -/
theorem hermitian_fourth_trace_markov {X I : Type*} [MeasurableSpace X] [Fintype I] [DecidableEq I]
    (μ : Measure X) [IsProbabilityMeasure μ] (M : X → Matrix I I ℂ)
    (hM : ∀ x,(M x).IsHermitian) (hi : Integrable (fun x => (Matrix.trace ((M x)^4)).re) μ)
    (t : ℝ) (ht : 0<t) :
    μ {x | t<‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) (M x)‖} ≤
      ENNReal.ofReal ((∫ x,(Matrix.trace ((M x)^4)).re∂μ)/t^4) := by
  have hs : {x | t<‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) (M x)‖} ⊆
      {x | t^4≤(Matrix.trace ((M x)^4)).re} := by
    intro x hx
    exact (pow_le_pow_left₀ ht.le hx.le 4).trans
      (hermitian_opNorm_even_power_le_trace (M x) (hM x) (by decide) (by decide))
  have hm := mul_meas_ge_le_integral_of_nonneg (μ:=μ)
    (Filter.Eventually.of_forall (fun x => hermitian_trace_fourth_nonneg (M x) (hM x))) hi (t^4)
  have hr : μ.real {x | t<‖Matrix.toEuclideanCLM (n:=I) (𝕜:=ℂ) (M x)‖} ≤
      (∫ x,(Matrix.trace ((M x)^4)).re∂μ)/t^4 :=
    (measureReal_mono hs).trans ((le_div_iff₀ (pow_pos ht 4)).mpr (by simpa only [mul_comm] using hm))
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hr

/-- The actual remainder operator-norm event is Borel, by its proved finite-polynomial representation. -/
theorem finiteComplementRemainder_bad_measurable
    {S K Ω : Type*} [Fintype S] [DecidableEq S] [Fintype K]
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω] (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (A : K → Finset S) (c : K → ℝ) (t : ℝ) :
    MeasurableSet {x | t<‖Matrix.toEuclideanCLM (n:=S → Fin d) (𝕜:=ℂ)
      (finiteComplementRemainder d μ record A c (complexCoordinate x))‖} :=
  (isOpen_lt continuous_const (finiteComplementRemainder_opNorm_continuous d μ record hr A c)).measurableSet

/-- The actual full-Haar cardinality-kernel remainder satisfies the operator-norm tail bound on its original Gaussian law. -/
theorem cardinalityHaar_remainder_tail (d n r : ℕ) [NeZero d] (hd : 3≤d)
    (lam : ℕ → ℝ) (t : ℝ) (ht : 0<t) :
    pairedGaussian (QuditIndex d n) {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal ((Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (complementLambda d n r lam)^8*(haarLocalKappa d)^(n-8*r)/t^4) := by
  let : IsProbabilityMeasure (pairedGaussian (QuditIndex d n)) := by unfold pairedGaussian; infer_instance
  have h := hermitian_fourth_trace_markov (pairedGaussian (QuditIndex d n)) _
    (fun x => cardinalityReadoutRemainder_isHermitian d (haarBasisRecords d) id continuous_id r lam
      (complexCoordinate x))
    (finiteComplementRemainder_fourth_integrable d (haarBasisRecords d) id continuous_id
      (cardinalityComplementSet (S:=Fin n) (r:=r)) (cardinalityComplementWeight lam)).re t ht
  exact h.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (by simpa only [Fintype.card_fin] using
      cardinalityHaar_remainder_bound (S:=Fin n) d hd r lam) (by positivity)))

/-- The identical actual operator event for the finite three-Pauli-basis ensemble. -/
theorem cardinalityPauli_remainder_tail (n r : ℕ) (lam : ℕ → ℝ) (t : ℝ) (ht : 0<t) :
    pairedGaussian (QuditIndex 2 n) {x | t<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal ((Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)*(complementLambda 2 n r lam)^8*
        pauliLocalKappa^(n-8*r)/t^4) := by
  let : IsProbabilityMeasure (pairedGaussian (QuditIndex 2 n)) := by unfold pairedGaussian; infer_instance
  have h := hermitian_fourth_trace_markov (pairedGaussian (QuditIndex 2 n)) _
    (fun x => cardinalityReadoutRemainder_isHermitian 2 pauliBasisRecords pauliFullRecord
      continuous_of_discreteTopology r lam (complexCoordinate x))
    (finiteComplementRemainder_fourth_integrable 2 pauliBasisRecords pauliFullRecord continuous_of_discreteTopology
      (cardinalityComplementSet (S:=Fin n) (r:=r)) (cardinalityComplementWeight lam)).re t ht
  exact h.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (by simpa only [Fintype.card_fin] using
      cardinalityPauli_remainder_bound (S:=Fin n) r lam) (by positivity)))

/-- At threshold n⁻³, the Gaussian tail bound for the Haar-readout remainder has fourth-moment factor n¹². -/
theorem cardinalityHaar_remainder_tail_n_inv_three (d n r : ℕ) [NeZero d] (hd : 3≤d)
    (hn : 0<n) (lam : ℕ → ℝ) :
    pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal ((n:ℝ)^12*(Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (complementLambda d n r lam)^8*(haarLocalKappa d)^(n-8*r)) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h := cardinalityHaar_remainder_tail d n r hd lam ((n:ℝ)^3)⁻¹ (by positivity)
  convert h using 1
  congr 1
  rw [div_eq_mul_inv,← inv_pow,inv_inv,← pow_mul]
  norm_num
  ring

/-- The same n^(-3) threshold and n^12 factor for the actual Pauli remainder. -/
theorem cardinalityPauli_remainder_tail_n_inv_three (n r : ℕ) (hn : 0<n) (lam : ℕ → ℝ) :
    pairedGaussian (QuditIndex 2 n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal ((n:ℝ)^12*(Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)*
        (complementLambda 2 n r lam)^8*pauliLocalKappa^(n-8*r)) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h := cardinalityPauli_remainder_tail n r lam ((n:ℝ)^3)⁻¹ (by positivity)
  convert h using 1
  congr 1
  rw [div_eq_mul_inv,← inv_pow,inv_inv,← pow_mul]
  norm_num
  ring

end CertificationGaussian
