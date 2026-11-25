import LocalCertification.Quantum.CompleteReadoutLoewner

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology ENNReal
noncomputable section
namespace LocalCertification.Quantum.CompleteLoewnerConsumers

/-- A sharp lower error is retained: the first eigenvalue falls from nu=5 to 4. -/
theorem two_dimensional_second_lower :
    (4:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)≤Matrix.diagonal ![4,9] ∧
    Matrix.diagonal ![4,9]≤(9:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have he : (Matrix.diagonal ![4,9] : Matrix (Fin 2) (Fin 2) ℂ)-
      ((5:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
        (1 : Matrix (Fin 2) (Fin 2) ℂ)*Matrix.diagonal ![0,3]*
          (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)=Matrix.diagonal ![-1,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  have hn : ‖(Matrix.diagonal ![4,9] : Matrix (Fin 2) (Fin 2) ℂ)-
      ((5:ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
        (1 : Matrix (Fin 2) (Fin 2) ℂ)*Matrix.diagonal ![0,3]*
          (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)‖≤1 := by
    rw [he,Matrix.l2_opNorm_diagonal]
    simp only [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)]
    intro i
    fin_cases i <;> norm_num
  have h := spectral_score_second_loewner (1 : Matrix (Fin 2) (Fin 2) ℂ) (by simp)
    ![0,3] 3 5 1 (by norm_num)
    (by intro j;fin_cases j <;> norm_num) (by intro j;fin_cases j <;> norm_num)
    (Matrix.diagonal ![4,9]) (by
      apply Matrix.isHermitian_diagonal_iff.mpr
      intro j
      fin_cases j <;> norm_num [IsSelfAdjoint]) hn
  norm_num at h ⊢
  exact h

/-- Empty ambient dimension requires no artificial nonempty premise. -/
theorem empty_hermitian_error (ε : ℝ) (hε : 0≤ε) :
    -(ε • (1 : Matrix (Fin 0) (Fin 0) ℂ))≤0 ∧
      (0 : Matrix (Fin 0) (Fin 0) ℂ)≤ε • 1 :=
  hermitian_norm_error_order 0 Matrix.isHermitian_zero ε (by simpa only [norm_zero] using hε)

/-- Signed original coefficients are allowed in the actual finite-Pauli event theorem. -/
theorem signed_pauli_scorebounds :
    ∃ η ε : ℕ → ℝ,(∀ n,0≤η n ∧ 0≤ε n) ∧
      Tendsto η atTop (nhds 0) ∧ Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex 2 n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex 2 n) bad≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
        ∀ U,U∉bad → completeReadoutLoewner 2 n 1 pauliBasisRecords pauliFullRecord
          (fun j => if j=0 then 1 else -2)
          (radialSecondCoefficientSup 2 1 (fun j => if j=0 then 1 else -2))
          (η n) (ε n) (haarPureVector ψ₀ U) :=
  completePauliReadout_scorebounds 1 _ (by simp)

end LocalCertification.Quantum.CompleteLoewnerConsumers
