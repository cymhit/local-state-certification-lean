import LocalCertification.Quantum.ShellReadoutExpansion

open scoped BigOperators ComplexOrder
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

/-- The unnormalized shell coefficient at distance k, including the k>j zero case. -/
def shellReadoutCoefficient (d n j k : ℕ) : ℝ :=
  if k ≤ j then (Nat.choose (n-k) (j-k) : ℝ) * (((d : ℝ)-1)^(j-k) * (d : ℝ)^k) else 0

variable {d : ℕ} [NeZero d] {n : ℕ}

/-- The complete shell acts on the actual product-basis projectors by a distance kernel. -/
theorem weylShell_projector (j : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (x : CertificationGaussian.QuditIndex d n) :
    (∑ u ∈ weylShell d n j,
      (quditWeyl u).conjTranspose * (productBasisPOVM d n U).effects x * quditWeyl u) =
      ∑ y : CertificationGaussian.QuditIndex d n,
        (shellReadoutCoefficient d n j (CertificationGaussian.hammingDistance x y) : ℂ) •
          (productBasisPOVM d n U).effects y := by
  have hf := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ (α := WeylLabel d n)) (Finset.univ.powersetCard j) weylSupport
    (fun u => (quditWeyl u).conjTranspose * (productBasisPOVM d n U).effects x * quditWeyl u)
  have he : (∑ u ∈ weylShell d n j,
      (quditWeyl u).conjTranspose * (productBasisPOVM d n U).effects x * quditWeyl u) =
      ∑ s ∈ Finset.univ.powersetCard j,
        ∑ u ∈ Finset.univ.filter (fun u : WeylLabel d n => weylSupport u = s),
          (quditWeyl u).conjTranspose * (productBasisPOVM d n U).effects x * quditWeyl u := by
    have hs : Finset.univ.filter (fun u : WeylLabel d n =>
        weylSupport u ∈ (Finset.univ (α := Fin n)).powersetCard j) = weylShell d n j := by
      unfold weylShell
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      exact Iff.rfl
    rw [hs] at hf
    exact hf.symm
  rw [he]
  simp_rw [fixedSupport_projector_outcomes]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.sum_smul, supportTransition_shell_sum]
  congr 1
  by_cases hk : CertificationGaussian.hammingDistance x y ≤ j <;> simp [shellReadoutCoefficient, hk]

/-- Cyclic trace identity uses conjugate transpose, without a Hermitian Weyl shortcut. -/
theorem weyl_conjugate_pairing (u : WeylLabel d n)
    (A B : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) :
    (quditWeyl u * A * (quditWeyl u).conjTranspose * B).trace =
      (A * ((quditWeyl u).conjTranspose * B * quditWeyl u)).trace := by
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (quditWeyl u) (A * (quditWeyl u).conjTranspose * B)

/-- The complex Born trace of the literal shell average has the actual distance coefficient. -/
theorem weylShellMatrix_pairing (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (j : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    (weylShellMatrix ρ j * (productBasisPOVM d n U).effects x).trace =
      ((weylShell d n j).card : ℝ)⁻¹ •
        ∑ y : CertificationGaussian.QuditIndex d n,
          (shellReadoutCoefficient d n j (CertificationGaussian.hammingDistance x y) : ℂ) *
            (ρ.matrix * (productBasisPOVM d n U).effects y).trace := by
  have h := congrArg (fun B => (ρ.matrix * B).trace) (weylShell_projector j U x)
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul] at h
  simp only [weylShellMatrix, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul,
    Matrix.trace_sum, weyl_conjugate_pairing]
  rw [h]

/-- The genuine mixed-state QIT Born distribution of a normalized shell. -/
theorem productBorn_shell_coefficient (hd : 2 ≤ d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (j : ℕ) (hj : j ≤ n)
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U (weylShellState hd ρ j hj) x =
      ((weylShell d n j).card : ℝ)⁻¹ *
        ∑ y : CertificationGaussian.QuditIndex d n,
          shellReadoutCoefficient d n j (CertificationGaussian.hammingDistance x y) * productBorn d n U ρ y := by
  unfold productBorn
  simp_rw [QIT.POVM.prob_eq_trace_re]
  change (weylShellMatrix ρ j * (productBasisPOVM d n U).effects x).trace.re = _
  rw [weylShellMatrix_pairing]
  simp [Complex.real_smul, Complex.re_sum]

end LocalCertification.Quantum
