import LocalCertification.Quantum.MeasurableShellReadout
import LocalCertification.Quantum.DualStates
import LocalCertification.Extremal.ResidualCancellation
import CertificationGaussian.CardinalityProjectorKernel
import LocalCertification.Quantum.MeasurablePOVMProductRefinement

/-! Original finite-dual states read out through arbitrary local rank-one effects.
The target, certificate, and physical state pair are fixed before the measurement.
The resulting complement matrix is exactly the kernel used by the Gaussian bounds. -/

open scoped BigOperators ComplexOrder
open Matrix Classical LocalCertification.Extremal
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum
variable {d n r : ℕ}

/-- The Gaussian cardinality kernel is the literal weighted sum of complement radii. -/
theorem cardinalityProjectorKernel_eq_complementRadius
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (J : Finset ℕ) (θ : ℕ → ℝ) :
    CertificationGaussian.cardinalityProjectorKernel P J θ =
      ∑ k ∈ J, θ k • complementRadius P k := by
  rw [CertificationGaussian.cardinalityProjectorKernel_formula]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (∑ A : {A : Finset (Fin n) // A.card = k},
      CertificationGaussian.projectorSubsetFactor P A.val) =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, complementTensor P A := by
    exact (Finset.sum_subtype (p := fun A : Finset (Fin n) => A.card = k)
      (Finset.univ.powersetCard k) (fun A => by simp) (complementTensor P)).symm
  rw [hs]
  simp only [Fintype.card_fin, complementRadius, smul_smul]
  ext x y
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_inv]
  ring

/-- The actual residual kernel has trace one, even for signed residual coefficients. -/
theorem dualComplementKernel_trace (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) r) (hN : c.maxNode ≤ n)
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (ht : ∀ i, (P i).trace = 1) :
    (CertificationGaussian.cardinalityProjectorKernel P (residualRadii c)
      (residualWeight d c)).trace = 1 := by
  rw [CertificationGaussian.cardinalityProjectorKernel_trace P ht (by simpa using hd)
    _ _ (fun k hk => by simpa using (Finset.mem_Icc.mp hk).2.trans hN)]
  rw [residualWeight_mass d (by omega) c, Complex.ofReal_one]

variable [NeZero d]

private theorem maximallyMixed_tensor_pairing
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (ht : ∀ i, (P i).trace = 1) :
    ((quditMaximallyMixed d n).matrix * tensorMatrix P).trace.re = ((d : ℝ)^n)⁻¹ := by
  rw [quditMaximallyMixed_matrix, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, tensorMatrix_trace]
  simp only [ht, Finset.prod_const_one, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]

/-- Exact physical high-minus-low readout, after all radii below the first residual cancel. -/
theorem dualStates_complement_difference (hd : 2 ≤ d)
    (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (ht : ∀ i, (P i).trace = 1) :
    (((dualHighState hd c ψ hN).matrix - (dualLowState hd c ψ hN).matrix) *
      tensorMatrix P).trace.re =
      (c.infinityWeight / dualNormalization ((d : ℝ)+1) r) *
        ((ψ.state.matrix - (quditMaximallyMixed d n).matrix) *
          CertificationGaussian.cardinalityProjectorKernel P (residualRadii c)
            (residualWeight d c)).trace.re := by
  have hs (i : Fin (r+1)) :
      ((pureTargetShell hd ψ (c.node i) ((c.node_le_maxNode i).trans hN)).matrix *
        tensorMatrix P).trace.re =
      ((d : ℝ)+1)^(-(c.node i : ℝ)) * ∑ k ∈ Finset.range (c.node i+1),
        ((c.node i).choose k : ℝ)*(d : ℝ)^k * (ψ.state.matrix * complementRadius P k).trace.re := by
    simpa only [pureTargetShell, inverse_pow_eq_real_decay] using
      weylShell_complement_readout hd ψ.state P ht (c.node i) ((c.node_le_maxNode i).trans hN)
  have hc := residual_cancellation_normalized d c
    (fun k => (ψ.state.matrix * complementRadius P k).trace.re)
  rw [complementRadius_zero] at hc
  have hcancel : (ψ.state.matrix * tensorMatrix P).trace.re -
      (∑ i, c.weight i * ((pureTargetShell hd ψ (c.node i)
        ((c.node_le_maxNode i).trans hN)).matrix * tensorMatrix P).trace.re) =
      c.infinityWeight * (ψ.state.matrix *
        CertificationGaussian.cardinalityProjectorKernel P (residualRadii c)
          (residualWeight d c)).trace.re := by
    rw [cardinalityProjectorKernel_eq_complementRadius]
    simpa only [hs, mul_assoc, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
      Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] using hc
  have hm : ((quditMaximallyMixed d n).matrix *
      CertificationGaussian.cardinalityProjectorKernel P (residualRadii c)
        (residualWeight d c)).trace.re = ((d : ℝ)^n)⁻¹ := by
    rw [quditMaximallyMixed_matrix, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, dualComplementKernel_trace hd c hN P ht]
    simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
  rw [dualStates_difference_explicit]
  simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.sum_mul, Matrix.trace_smul,
    Matrix.trace_sub, Matrix.trace_sum, Complex.smul_re, Complex.sub_re, Complex.re_sum, smul_eq_mul]
  rw [maximallyMixed_tensor_pairing P ht, hcancel, hm]
  ring

/-- The original pair's actual refined Born densities have the same fixed residual kernel. -/
theorem dualStates_refinedBornDensity_difference
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (hd : 2 ≤ d) (c : IntegerDualCertificate ((d : ℝ)+1) r)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : c.maxNode ≤ n)
    (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)) (s : (i : Fin n) → Ω i × Fin d) :
    MeasurablePOVM.productRefinedBornDensity M (dualHighState hd c ψ hN) s -
      MeasurablePOVM.productRefinedBornDensity M (dualLowState hd c ψ hN) s =
      (c.infinityWeight / dualNormalization ((d : ℝ)+1) r) * (d : ℝ)^n *
        ((ψ.state.matrix - (quditMaximallyMixed d n).matrix) *
          CertificationGaussian.cardinalityProjectorKernel
            (fun i => (M i).refinementProjector (s i).1 (s i).2) (residualRadii c)
            (residualWeight d c)).trace.re := by
  have hdiff := dualStates_complement_difference hd c ψ hN
    (fun i => (M i).refinementProjector (s i).1 (s i).2)
    (fun i => (M i).refinementProjector_trace (s i).1 (s i).2)
  rw [MeasurablePOVM.productRefinedBornDensity_eq, MeasurablePOVM.productRefinedBornDensity_eq,
    ← mul_sub, ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
  change (Fintype.card (Fin n → Fin d) : ℝ) *
    ((((dualHighState hd c ψ hN).matrix - (dualLowState hd c ψ hN).matrix) *
      tensorMatrix (fun i => (M i).refinementProjector (s i).1 (s i).2)).trace.re) = _
  rw [hdiff]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  ring

end LocalCertification.Quantum
