import LocalCertification.Quantum.ProductMeasurement
import CertificationGaussian.Consumers.HaarMoments

open scoped BigOperators
open Matrix MeasureTheory Metric Set
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual normalized sphere vector, with its same amplitudes, as a QIT pure vector. -/
def spherePureVector (ψ : sphere (0 : EuclideanSpace ℂ I) 1) : QIT.PureVector I where
  amp := ψ.val
  trace_rankOne_eq_one := by
    rw [rankOne_trace_norm_sq]
    have h := mem_sphere_zero_iff_norm.mp ψ.property
    change (‖ψ.val‖ ^ 2 : ℂ) = 1
    rw [h]
    norm_num

@[simp] theorem spherePureVector_amp (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    (spherePureVector ψ).amp = ψ.val := rfl

omit [DecidableEq I] in
/-- Rank-one trace overlap is the squared modulus of the actual Euclidean inner product. -/
theorem rankOne_pairing (v w : I → ℂ) :
    (QIT.rankOneMatrix v * QIT.rankOneMatrix w).trace =
      (Complex.normSq (inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ I)
        (WithLp.toLp 2 w : EuclideanSpace ℂ I)) : ℂ) := by
  simp only [QIT.rankOneMatrix, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Pi.star_apply, Complex.star_def,
    Finset.sum_mul, Finset.mul_sum, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- No Hermitian hypothesis on W is used in the pure-state conjugation overlap. -/
theorem pure_conjugate_pairing (ψ : QIT.PureVector I) (W : Matrix I I ℂ) :
    (ψ.state.matrix * (W * ψ.state.matrix * W.conjTranspose)).trace.re =
      Complex.normSq (inner ℂ (WithLp.toLp 2 ψ.amp : EuclideanSpace ℂ I)
        (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) W (WithLp.toLp 2 ψ.amp))) := by
  rw [QIT.PureVector.state_matrix, matrix_conjugate_rankOne, rankOne_pairing]
  rfl

variable {d : ℕ} [NeZero d] {n : ℕ}

/-- Every nonidentity canonical Weyl matrix is traceless, including composite dimensions. -/
theorem quditWeyl_trace_zero {u : WeylLabel d n} (hu : u ≠ 0) :
    (quditWeyl u).trace = 0 := by
  simpa [eq_comm, hu] using quditWeyl_hilbertSchmidt (0 : WeylLabel d n) u

/-- The actual nonidentity Weyl overlap under full-unitary Haar sampling. -/
theorem haar_quditWeyl_overlap {u : WeylLabel d n} (hu : u ≠ 0)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :
    ∫ U, Complex.normSq (inner ℂ
      (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) U ψ : EuclideanSpace ℂ _)
      (Matrix.toEuclideanCLM (n := CertificationGaussian.QuditIndex d n) (𝕜 := ℂ) (quditWeyl u)
        (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) U ψ)))
      ∂CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n) = ((d : ℝ)^n + 1)⁻¹ := by
  let : Nonempty (CertificationGaussian.QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  simpa [qudit_card, Nat.cast_pow] using
    CertificationGaussian.Consumers.haar_traceless_unitary_overlap (quditWeyl u)
      ⟨quditWeyl_adjoint_mul u, quditWeyl_mul_adjoint u⟩ (quditWeyl_trace_zero hu) ψ

/-- Literal shell-state fidelity is the average of the actual Weyl overlaps. -/
theorem pureTargetShell_fidelity (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (j : ℕ) (hj : j ≤ n) :
    pureTargetFidelity ψ (pureTargetShell hd ψ j hj) =
      ((weylShell d n j).card : ℝ)⁻¹ * ∑ u ∈ weylShell d n j,
        Complex.normSq (inner ℂ (WithLp.toLp 2 ψ.amp : EuclideanSpace ℂ _)
          (Matrix.toEuclideanCLM (n := CertificationGaussian.QuditIndex d n) (𝕜 := ℂ)
            (quditWeyl u) (WithLp.toLp 2 ψ.amp))) := by
  change (ψ.state.matrix * weylShellMatrix ψ.state j).trace.re = _
  simp only [weylShellMatrix, Matrix.mul_smul, Finset.mul_sum, Matrix.trace_smul,
    Matrix.trace_sum, Complex.re_sum, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [pure_conjugate_pairing]

/-- The actual Haar overlap integrands are integrable, independently of the label. -/
theorem haar_quditWeyl_overlap_integrable (u : WeylLabel d n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :
    Integrable (fun U => Complex.normSq (inner ℂ
      (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) U ψ : EuclideanSpace ℂ _)
      (Matrix.toEuclideanCLM (n := CertificationGaussian.QuditIndex d n) (𝕜 := ℂ) (quditWeyl u)
        (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) U ψ))))
      (CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)) := by
  simp_rw [← CertificationGaussian.sphereQuadraticForm_eq_inner]
  have hc : Continuous (fun U : CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n) =>
      (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) U ψ :
        EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))) :=
    by
      simp only [CertificationGaussian.complexUnitarySphereAction_coe]
      fun_prop
  exact (Complex.continuous_normSq.comp
    ((CertificationGaussian.sphereQuadraticForm_continuous _).comp hc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The same Haar-random unit vector as a genuine QIT pure target. -/
def haarPureVector (ψ : sphere (0 : EuclideanSpace ℂ I) 1)
    (U : CertificationGaussian.ComplexUnitary I) : QIT.PureVector I :=
  spherePureVector (CertificationGaussian.complexUnitarySphereAction I U ψ)

/-- Every nonzero support shell has mean pure-target fidelity exactly 1/(d^n+1).
The target itself is the same Haar-random pure vector used to form the physical shell state. -/
theorem haar_pureTargetShell_fidelity (hd : 2 ≤ d) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :
    ∫ U, pureTargetFidelity (haarPureVector ψ U)
      (pureTargetShell hd (haarPureVector ψ U) j hj)
      ∂CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n) = ((d : ℝ)^n + 1)⁻¹ := by
  simp_rw [pureTargetShell_fidelity]
  dsimp only [haarPureVector]
  rw [integral_const_mul, integral_finsetSum]
  · have hnz (u : WeylLabel d n) (hu : u ∈ weylShell d n j) : u ≠ 0 := by
      intro h
      subst u
      have hw := (Finset.mem_filter.mp hu).2
      simp [weylWeight, weylSupport] at hw
      omega
    have he : (∑ u ∈ weylShell d n j, ∫ U, Complex.normSq (inner ℂ
        (WithLp.toLp 2 (spherePureVector (CertificationGaussian.complexUnitarySphereAction
          (CertificationGaussian.QuditIndex d n) U ψ)).amp : EuclideanSpace ℂ _)
        (Matrix.toEuclideanCLM (n := CertificationGaussian.QuditIndex d n) (𝕜 := ℂ) (quditWeyl u)
          (WithLp.toLp 2 (spherePureVector (CertificationGaussian.complexUnitarySphereAction
            (CertificationGaussian.QuditIndex d n) U ψ)).amp)))
        ∂CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)) =
        ∑ _u ∈ weylShell d n j, ((d : ℝ)^n+1)⁻¹ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact haar_quditWeyl_overlap (hnz u hu) ψ
    rw [he]
    have hc : ((weylShell d n j).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (weylShell_card_pos hd hj))
    simp [hc]
  · intro u _
    exact haar_quditWeyl_overlap_integrable u ψ

/-- This expectation is for QIT squared fidelity, via the proved pure-target bridge. -/
theorem haar_pureTargetShell_squaredFidelity (hd : 2 ≤ d) {j : ℕ}
    (hj0 : 0 < j) (hj : j ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :
    ∫ U, (pureTargetShell hd (haarPureVector ψ U) j hj).squaredFidelity
      (haarPureVector ψ U).state
      ∂CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n) = ((d : ℝ)^n + 1)⁻¹ := by
  simp_rw [← pureTargetFidelity_eq_squaredFidelity]
  exact haar_pureTargetShell_fidelity hd hj0 hj ψ

/-- Positivity here follows termwise from the literal shell overlap formula. -/
theorem pureTargetShell_fidelity_nonneg (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (j : ℕ) (hj : j ≤ n) :
    0 ≤ pureTargetFidelity ψ (pureTargetShell hd ψ j hj) := by
  rw [pureTargetShell_fidelity]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

/-- The actual shell fidelity is integrable under genuine full-unitary Haar sampling. -/
theorem haar_pureTargetShell_fidelity_integrable (hd : 2 ≤ d) (j : ℕ) (hj : j ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :
    Integrable (fun U => pureTargetFidelity (haarPureVector ψ U)
      (pureTargetShell hd (haarPureVector ψ U) j hj))
      (CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)) := by
  simp_rw [pureTargetShell_fidelity]
  exact (integrable_finsetSum _ (fun u _ => haar_quditWeyl_overlap_integrable u ψ)).const_mul _

/-- The zero shell is the target itself and has fidelity one, including n=0. -/
theorem pureTargetShell_zero_fidelity (hd : 2 ≤ d)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) :
    pureTargetFidelity ψ (pureTargetShell hd ψ 0 (Nat.zero_le n)) = 1 := by
  rw [pureTargetShell_zero]
  unfold pureTargetFidelity
  rw [ψ.state_matrix_mul_self, ψ.state.trace_eq_one]
  rfl

end LocalCertification.Quantum
