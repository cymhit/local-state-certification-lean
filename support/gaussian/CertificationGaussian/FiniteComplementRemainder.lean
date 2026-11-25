import CertificationGaussian.ReadoutRemainderFourthMoment

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace CertificationGaussian

/-- Fourth powers of actual Hermitian complex matrices have nonnegative real trace. -/
theorem hermitian_trace_fourth_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (hM : M.IsHermitian) : 0≤(Matrix.trace (M^4)).re := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self (M^2)
  simp only [Matrix.conjTranspose_pow,hM.eq,← pow_add,show 2+2=4 by decide] at hp
  exact (RCLike.nonneg_iff.mp hp.trace_nonneg).1

theorem hermitian_trace_fourth_im_zero {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (hM : M.IsHermitian) : (Matrix.trace (M^4)).im=0 := by
  apply (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
  change star (Matrix.trace (M^4))=Matrix.trace (M^4)
  rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_pow,hM.eq]

variable {S K : Type*} [Fintype S] [DecidableEq S] [Fintype K]

/-- The true Gaussian expectation of Tr(Z_z^4), for the actual Haar finite-complement readout remainder. -/
theorem finiteComplementHaar_remainder_norm_bound (d : ℕ) [NeZero d] (hd : 3≤d)
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    ‖∫ z,Matrix.trace ((finiteComplementRemainder d (haarBasisRecords d) id A c
      (complexCoordinate z))^4) ∂pairedGaussian (S → Fin d)‖ ≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (∑ k,|c k|)^8*(haarLocalKappa d)^(Fintype.card S-8*r) := by
  rw [finiteComplementRemainder_fourth_expectation d (haarBasisRecords d) id continuous_id]
  exact finiteComplementHaarGaussianFourthIntegral_bound d hd r A hA c

/-- The paper's real expected fourth trace bound, with the full Haar basis/outcome records retained. -/
theorem finiteComplementHaar_remainder_bound (d : ℕ) [NeZero d] (hd : 3≤d)
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    (∫ z,(Matrix.trace ((finiteComplementRemainder d (haarBasisRecords d) id A c
      (complexCoordinate z))^4)).re ∂pairedGaussian (S → Fin d)) ≤
      (Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)*
        (∑ k,|c k|)^8*(haarLocalKappa d)^(Fintype.card S-8*r) := by
  exact (integral_re (finiteComplementRemainder_fourth_integrable d (haarBasisRecords d) id
    continuous_id A c)).trans_le
      ((Complex.re_le_norm _).trans (finiteComplementHaar_remainder_norm_bound d hd r A hA c))

/-- The true Gaussian expectation of Tr(Z_z^4), for the actual finite six-record Pauli ensemble. -/
theorem finiteComplementPauli_remainder_norm_bound
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    ‖∫ z,Matrix.trace ((finiteComplementRemainder 2 pauliBasisRecords pauliFullRecord A c
      (complexCoordinate z))^4) ∂pairedGaussian (S → Fin 2)‖ ≤
      (Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)*(∑ k,|c k|)^8*
        pauliLocalKappa^(Fintype.card S-8*r) := by
  have he := finiteComplementRemainder_fourth_expectation 2 pauliBasisRecords pauliFullRecord
    continuous_of_discreteTopology A c
  rw [he]
  exact finiteComplementPauliGaussianFourthIntegral_bound r A hA c

/-- The qubit real fourth-moment remainder bound is proved on the actual Pauli records, with strict κ2. -/
theorem finiteComplementPauli_remainder_bound
    (r : ℕ) (A : K → Finset S) (hA : ∀ k,(A k).card≤r) (c : K → ℝ) :
    (∫ z,(Matrix.trace ((finiteComplementRemainder 2 pauliBasisRecords pauliFullRecord A c
      (complexCoordinate z))^4)).re ∂pairedGaussian (S → Fin 2)) ≤
      (Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)*(∑ k,|c k|)^8*
        pauliLocalKappa^(Fintype.card S-8*r) := by
  exact (integral_re (finiteComplementRemainder_fourth_integrable 2 pauliBasisRecords pauliFullRecord
    continuous_of_discreteTopology A c)).trans_le
      ((Complex.re_le_norm _).trans (finiteComplementPauli_remainder_norm_bound r A hA c))

end CertificationGaussian
