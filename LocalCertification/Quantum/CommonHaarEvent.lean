import LocalCertification.Quantum.CalibrationFloor
import LocalCertification.Quantum.DualKernelOrder
import LocalCertification.Quantum.HaarShellControl
import LocalCertification.Quantum.HaarProductBasis

set_option autoImplicit false
open scoped BigOperators ENNReal
open Matrix LocalCertification.Extremal MeasureTheory Metric Set
noncomputable section
namespace LocalCertification.Quantum

variable {d : ℕ} [NeZero d] {n : ℕ}

/-- One actual Haar target event controls the fixed dual shells and all continuous product bases. -/
def dualHaarGoodEvent (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (C t : ℝ) :
    Set (CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n)) :=
  {W | (∀ i : Fin (r+1), pureTargetFidelity (haarPureVector ψ W)
      (pureTargetShell hd (haarPureVector ψ W) ((quditDualCertificate hd r).node i)
        (((quditDualCertificate hd r).node_le_maxNode i).trans hN)) ≤ t) ∧
    ∀ U : Fin n → CertificationGaussian.LocalUnitary d,
      (d : ℝ)^n * ‖CertificationGaussian.processedProbability (tensorBasis d n (qitProductBasis d n U))
        (CertificationGaussian.signedHammingKernel d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r)))
        (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ)‖^2 ≤
      (1+C/n)*CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
        (residualWeight d (quditDualCertificate hd r))}

/-- The r+1 actual dual nodes obey one finite union bound under the same Haar measure. -/
theorem dualHaar_shell_failure (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) {t : ℝ} (ht : 0 < t) :
    CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
      {W | ∃ i : Fin (r+1), t < pureTargetFidelity (haarPureVector ψ W)
        (pureTargetShell hd (haarPureVector ψ W) ((quditDualCertificate hd r).node i)
          (((quditDualCertificate hd r).node_le_maxNode i).trans hN))} ≤
      ENNReal.ofReal (((r+1 : ℕ) : ℝ)/(t*((d : ℝ)^n+1))) := by
  rw [Set.ofPred_exists]
  calc
    _ ≤ ∑ i : Fin (r+1), CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n)
      {W | t < pureTargetFidelity (haarPureVector ψ W)
        (pureTargetShell hd (haarPureVector ψ W) ((quditDualCertificate hd r).node i)
          (((quditDualCertificate hd r).node_le_maxNode i).trans hN))} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (r+1), ENNReal.ofReal (1/(t*((d : ℝ)^n+1))) := by
      apply Finset.sum_le_sum
      intro i _
      exact haar_shell_failure hd ((quditDualCertificate hd r).node_pos i)
        (((quditDualCertificate hd r).node_le_maxNode i).trans hN) ψ ht
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

/-- Constants and cutoff are fixed before the target; one event controls both required properties.
The threshold remains arbitrary, so polynomial and exponential failure cutoffs use the same theorem. -/
theorem dualHaar_common_event (hd : 2 ≤ d) (r : ℕ) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1,
      ∀ t : ℝ, 0 < t → ∃ hN : (quditDualCertificate hd r).maxNode ≤ n,
      CertificationGaussian.complexUnitaryHaar (CertificationGaussian.QuditIndex d n) (dualHaarGoodEvent hd r ψ hN C t)ᶜ ≤
        ENNReal.ofReal (((r+1 : ℕ) : ℝ)/(t*((d : ℝ)^n+1))) +
        ENNReal.ofReal (Real.exp (-a*(n : ℝ)^3)) := by
  obtain ⟨a, C, ha, hC, N, hP⟩ := qudit_haar_product_basis_score_bound d hd
    (residualRadii (quditDualCertificate hd r)) (residualWeight d (quditDualCertificate hd r))
    (residualWeight_mass d (by omega) (quditDualCertificate hd r))
  refine ⟨a, C, ha, hC, max N (quditDualCertificate hd r).maxNode, ?_⟩
  intro n hn ψ t ht
  have hnP : N ≤ n := le_trans (le_max_left _ _) hn
  have hN : (quditDualCertificate hd r).maxNode ≤ n := le_trans (le_max_right _ _) hn
  refine ⟨hN, ?_⟩
  have hs := dualHaar_shell_failure hd r ψ hN ht
  have hp := hP n hnP ψ
  apply le_trans (measure_mono (show (dualHaarGoodEvent hd r ψ hN C t)ᶜ ⊆
      {W | ∃ i : Fin (r+1), t < pureTargetFidelity (haarPureVector ψ W)
        (pureTargetShell hd (haarPureVector ψ W) ((quditDualCertificate hd r).node i)
          (((quditDualCertificate hd r).node_le_maxNode i).trans hN))} ∪
      {W | ∃ U : Fin n → CertificationGaussian.LocalUnitary d,
        (1+C/n)*CertificationGaussian.kernelVarianceScale d n (residualRadii (quditDualCertificate hd r))
          (residualWeight d (quditDualCertificate hd r)) <
        (d : ℝ)^n * ‖CertificationGaussian.processedProbability (tensorBasis d n (qitProductBasis d n U))
          (CertificationGaussian.signedHammingKernel d n (residualRadii (quditDualCertificate hd r))
            (residualWeight d (quditDualCertificate hd r)))
          (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ)‖^2} from ?_))
  · exact (measure_union_le _ _).trans (add_le_add hs hp)
  · intro W hW
    change ¬ (_ ∧ _) at hW
    rcases not_and_or.mp hW with h | h
    · left
      simpa only [Set.mem_ofPred_eq, not_forall, not_le] using h
    · right
      simpa only [Set.mem_ofPred_eq, not_forall, not_le] using h

/-- On the joint event the actual chosen low-state overlap is small, including the uniform atom. -/
theorem dualHaarGoodEvent_low_fidelity (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (C t : ℝ)
    (hD : ((d : ℝ)^n)⁻¹ ≤ t) (W : CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n))
    (hW : W ∈ dualHaarGoodEvent hd r ψ hN C t) :
    uncalibratedLowFidelity hd r (haarPureVector ψ W) hN ≤ t :=
  dualLowState_fidelity_le hd (quditDualCertificate hd r) _ hN hD hW.1

/-- Shell overlap is continuous in the actual Haar unitary, hence has no measurability gap. -/
theorem haar_pureTargetShell_fidelity_continuous (hd : 2 ≤ d) (j : ℕ) (hj : j ≤ n)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :
    Continuous (fun W => pureTargetFidelity (haarPureVector ψ W)
      (pureTargetShell hd (haarPureVector ψ W) j hj)) := by
  have hc : Continuous (fun W : CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n) =>
      (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ :
        EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))) := by
    simp only [CertificationGaussian.complexUnitarySphereAction_coe]
    fun_prop
  have ht (u : WeylLabel d n) : Continuous (fun W : CertificationGaussian.ComplexUnitary (CertificationGaussian.QuditIndex d n) =>
      Complex.normSq (inner ℂ
        (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ : EuclideanSpace ℂ _)
        (Matrix.toEuclideanCLM (n := CertificationGaussian.QuditIndex d n) (𝕜 := ℂ) (quditWeyl u)
          (CertificationGaussian.complexUnitarySphereAction (CertificationGaussian.QuditIndex d n) W ψ)))) :=
    Complex.continuous_normSq.comp (hc.inner
      ((Matrix.toEuclideanCLM (n := CertificationGaussian.QuditIndex d n) (𝕜 := ℂ) (quditWeyl u)).continuous.comp hc))
  have hs := (continuous_finsetSum (weylShell d n j) (fun u _ => ht u)).const_mul
    (((weylShell d n j).card : ℝ)⁻¹)
  convert hs using 1
  ext W
  exact pureTargetShell_fidelity hd (haarPureVector ψ W) j hj

/-- The all-bases quantifier is an arbitrary intersection of closed sets, not a finite-net event. -/
theorem dualHaarGoodEvent_isClosed (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (C t : ℝ) :
    IsClosed (dualHaarGoodEvent hd r ψ hN C t) := by
  unfold dualHaarGoodEvent
  rw [Set.ofPred_and]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le (haar_pureTargetShell_fidelity_continuous hd _ _ ψ) continuous_const
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro U
    apply isClosed_le _ continuous_const
    simp only [CertificationGaussian.processedProbability, CertificationGaussian.complexUnitarySphereAction_coe]
    fun_prop

theorem dualHaarGoodEvent_measurableSet (hd : 2 ≤ d) (r : ℕ)
    (ψ : sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)
    (hN : (quditDualCertificate hd r).maxNode ≤ n) (C t : ℝ) :
    MeasurableSet (dualHaarGoodEvent hd r ψ hN C t) :=
  (dualHaarGoodEvent_isClosed hd r ψ hN C t).measurableSet

end LocalCertification.Quantum
