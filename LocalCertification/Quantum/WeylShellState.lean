import LocalCertification.Quantum.WeylSupport
import LocalCertification.Quantum.Boundary

open scoped BigOperators ComplexOrder
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

variable {d : ℕ} [NeZero d] {n : ℕ}

/-- Unitary conjugation preserves the actual density matrix trace. -/
theorem quditWeyl_conjugate_trace (u : WeylLabel d n)
    (A : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) :
    (quditWeyl u * A * (quditWeyl u).conjTranspose).trace = A.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, quditWeyl_adjoint_mul, Matrix.one_mul]

/-- The literal uniform average of Weyl conjugates in one support shell. -/
def weylShellMatrix (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : ℕ) :
    Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ :=
  ((weylShell d n j).card : ℝ)⁻¹ •
    ∑ u ∈ weylShell d n j, quditWeyl u * ρ.matrix * (quditWeyl u).conjTranspose

theorem weylShellMatrix_pos (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : ℕ) :
    (weylShellMatrix ρ j).PosSemidef := by
  have hs (s : Finset (WeylLabel d n)) :
      (∑ u ∈ s, quditWeyl u * ρ.matrix * (quditWeyl u).conjTranspose).PosSemidef := by
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero (n := CertificationGaussian.QuditIndex d n) (R := ℂ))
    | @insert u s hu ih =>
      rw [Finset.sum_insert hu]
      exact (ρ.pos.mul_mul_conjTranspose_same (quditWeyl u)).add ih
  exact (hs _).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem weylShellMatrix_trace (hd : 2 ≤ d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) {j : ℕ} (hj : j ≤ n) :
    (weylShellMatrix ρ j).trace = 1 := by
  have hc : ((weylShell d n j).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (weylShell_card_pos hd hj))
  simp only [weylShellMatrix, Matrix.trace_smul, Matrix.trace_sum,
    quditWeyl_conjugate_trace, ρ.trace_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Complex.real_smul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hc, Complex.ofReal_one]

/-- A QIT density state, with positivity and normalization proved from the actual shell average. -/
def weylShellState (hd : 2 ≤ d) (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (j : ℕ) (hj : j ≤ n) : QIT.State (CertificationGaussian.QuditIndex d n) where
  matrix := weylShellMatrix ρ j
  pos := weylShellMatrix_pos ρ j
  trace_eq_one := weylShellMatrix_trace hd ρ hj

/-- The normalization is exactly binomial(n,j)*(d^2-1)^j from the paper. -/
theorem weylShellState_matrix (hd : 2 ≤ d) (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (j : ℕ) (hj : j ≤ n) :
    (weylShellState hd ρ j hj).matrix =
      ((Nat.choose n j * (d^2 - 1)^j : ℕ) : ℝ)⁻¹ •
        ∑ u ∈ weylShell d n j, quditWeyl u * ρ.matrix * (quditWeyl u).conjTranspose := by
  simp [weylShellState, weylShellMatrix, weylShell_card]

@[simp] theorem weylShellMatrix_zero (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    weylShellMatrix ρ 0 = ρ.matrix := by
  simp [weylShellMatrix]

@[simp] theorem weylShellState_zero (hd : 2 ≤ d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    weylShellState hd ρ 0 (Nat.zero_le n) = ρ := by
  apply QIT.State.ext
  exact weylShellMatrix_zero ρ

/-- The paper's pure-target shell is an actual QIT state, without adding positivity assumptions. -/
def pureTargetShell (hd : 2 ≤ d) (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (j : ℕ) (hj : j ≤ n) : QIT.State (CertificationGaussian.QuditIndex d n) :=
  weylShellState hd ψ.state j hj

@[simp] theorem pureTargetShell_zero (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) :
    pureTargetShell hd ψ 0 (Nat.zero_le n) = ψ.state := by
  exact weylShellState_zero hd ψ.state

end LocalCertification.Quantum
