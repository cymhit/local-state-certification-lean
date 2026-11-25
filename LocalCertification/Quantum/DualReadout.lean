import LocalCertification.Quantum.DualStates
import LocalCertification.Quantum.ShellReadoutNormalization
import LocalCertification.Extremal.ResidualCancellation

set_option autoImplicit false
open scoped BigOperators ComplexOrder
open Matrix LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Quantum

variable {d : ℕ} [NeZero d] {n r : ℕ}

omit [NeZero d] in
theorem productBorn_trace_formula (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U ρ x = (ρ.matrix * (productBasisPOVM d n U).effects x).trace.re :=
  (productBasisPOVM d n U).prob_eq_trace_re ρ x

theorem productBorn_maximallyMixed (U : Fin n → CertificationGaussian.LocalUnitary d)
    (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U (quditMaximallyMixed d n) x = ((d : ℝ)^n)⁻¹ := by
  rw [productBorn_trace_formula, quditMaximallyMixed_matrix, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul]
  change (((d : ℝ)^n)⁻¹ • ((basisPOVM _).effects x).trace).re = _
  rw [basisPOVM_effect_trace]
  simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]

/-- Actual Born-law difference in every product basis, before shell cancellation. -/
theorem dualStates_productBorn_raw (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U (dualHighState hd c ψ hN) x -
      productBorn d n U (dualLowState hd c ψ hN) x =
      (dualNormalization ((d : ℝ)+1) r)⁻¹ *
        (productBorn d n U ψ.state x -
          (∑ i, c.weight i * productBorn d n U
            (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)) x) -
          c.infinityWeight * ((d : ℝ)^n)⁻¹) := by
  simp_rw [productBorn_trace_formula]
  rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul, dualStates_difference_explicit]
  simp only [Matrix.smul_mul, Matrix.sub_mul, Finset.sum_mul, Matrix.trace_smul,
    Matrix.trace_sub, Matrix.trace_sum, Complex.smul_re, Complex.sub_re, Complex.re_sum, smul_eq_mul]
  simp_rw [← productBorn_trace_formula]
  rw [productBorn_maximallyMixed]

/-- Radius zero of the unique Hamming-average model is the identity matrix. -/
theorem distanceAverage_zero (d n : ℕ) : CertificationGaussian.distanceAverage d n 0 =
    (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℝ) := by
  classical
  ext x y
  simp [CertificationGaussian.distanceAverage, CertificationGaussian.hammingDistance_eq_hammingDist,
    hammingDist_eq_zero, Matrix.one_apply]

omit [NeZero d] in
/-- Multiplication by the existing signed Hamming kernel is the literal weighted radius sum. -/
theorem signedHammingKernel_mulVec (J : Finset ℕ) (θ : ℕ → ℝ)
    (p : CertificationGaussian.QuditIndex d n → ℝ) (x : CertificationGaussian.QuditIndex d n) :
    (CertificationGaussian.signedHammingKernel d n J θ).mulVec p x =
      ∑ k ∈ J, θ k * (CertificationGaussian.distanceAverage d n k).mulVec p x := by
  simp only [CertificationGaussian.signedHammingKernel, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The physical high/low readout difference equals the signed Hamming kernel used in the uniform score bound,
for every continuous product basis, with no target-dependent choice of coefficients. -/
theorem dualStates_productBorn_difference (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    productBorn d n U (dualHighState hd c ψ hN) x -
      productBorn d n U (dualLowState hd c ψ hN) x =
      (c.infinityWeight / dualNormalization ((d : ℝ)+1) r) *
        ((CertificationGaussian.signedHammingKernel d n (residualRadii c) (residualWeight d c)).mulVec
          (productBorn d n U ψ.state) x - ((d : ℝ)^n)⁻¹) := by
  have hs (i : Fin (r+1)) : productBorn d n U
      (pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)) x =
      ((d : ℝ)+1)^(-(c.node i : ℝ)) * ∑ k ∈ Finset.range (c.node i+1),
        ((c.node i).choose k : ℝ)*(d : ℝ)^k *
          (CertificationGaussian.distanceAverage d n k).mulVec (productBorn d n U ψ.state) x := by
    simpa only [pureTargetShell, inverse_pow_eq_real_decay] using
      productBorn_shell_readout hd ψ.state (c.node i) ((c.node_le_maxNode i).trans hN) U x
  rw [dualStates_productBorn_raw, signedHammingKernel_mulVec]
  simp_rw [hs, ← mul_assoc]
  have hc := residual_cancellation_normalized d c
    (fun k => (CertificationGaussian.distanceAverage d n k).mulVec (productBorn d n U ψ.state) x)
  rw [distanceAverage_zero, Matrix.one_mulVec] at hc
  rw [hc]
  ring

omit [NeZero d] in
/-- The instantiated residual kernel preserves constants in every legal system size. -/
theorem dualResidualKernel_preserves_constants (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) r) (hN : c.maxNode ≤ n) :
    (CertificationGaussian.signedHammingKernel d n (residualRadii c) (residualWeight d c)).mulVec
      (fun _ => (1 : ℝ)) = fun _ => 1 := by
  apply CertificationGaussian.signedHammingKernel_preserves_constants hd
  · intro k hk
    exact (Finset.mem_Icc.mp hk).2.trans hN
  · exact residualWeight_mass d (by omega) c

end LocalCertification.Quantum
