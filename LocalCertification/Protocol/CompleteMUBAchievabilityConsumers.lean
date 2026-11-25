import LocalCertification.Protocol.CompleteMUBAchievability
import CertificationGaussian.Consumers.CompleteMUB
import LocalCertification.Extremal.DegreeZero

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.CompleteMUBConsumers

/-- The supplied actual Z/X/Y complete MUB uses exactly the original physical Pauli experiment. -/
theorem actual_pauli_full_born_law (n : ℕ) (ρ : QIT.State (QuditIndex 2 n)) :
    completeMUBBornLaw CertificationGaussian.Consumers.actualPauliMUB n ρ=
      completeBornRecordLaw ρ (localProductSetting pauliBasisUnitary)
        (localProductSetting_continuous pauliBasisUnitary continuous_of_discreteTopology).measurable
        (Measure.pi (fun _ : Fin n => uniformFiniteOutcome 3)) := rfl

/-- The actual complete-MUB route admits signed coefficients, with no design or control premise. -/
theorem actual_pauli_signed_canonical :
    FixedScoreCanonicalConclusion CertificationGaussian.Consumers.actualPauliMUB.basis continuous_of_discreteTopology
      (uniformFiniteOutcome 3) 1 (fun j => if j=0 then 1 else -2) :=
  fixedScore_completeMUB_canonical 2 1 (by norm_num) CertificationGaussian.Consumers.actualPauliMUB _ (by simp)

/-- The empty-system and one-dimensional boundary retain the true full second moment. -/
theorem zero_sites_full_second (ρ : QIT.State (QuditIndex 1 0)) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex 1 0)) :
    ∫ z,(cardinalityBornScore CertificationGaussian.Consumers.oneDimensionalMUB.basis 0 lam ψ z)^2
      ∂completeMUBBornLaw CertificationGaussian.Consumers.oneDimensionalMUB 0 ρ=
      (Matrix.trace (ρ.matrix*cardinalityReadoutSecond 1 (completeMUBRecords 1)
        (completeMUBFullRecord CertificationGaussian.Consumers.oneDimensionalMUB) 0 lam 1 ψ.ofLp)).re := by
  simpa only [pow_zero] using completeMUBBornScore_second CertificationGaussian.Consumers.oneDimensionalMUB ρ 0 lam ψ

/-- A concrete degree-zero window exercises the actual MUB test and constant-in-n sample bound. -/
theorem actual_pauli_degree_zero_budget :
    ∃ (lam : ℕ → ℝ) (good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1))
      (K : ℝ),0<K ∧ (∀ n,IsCompact (good n)) ∧ ∀ᶠ n : ℕ in atTop,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 n)) (good n)ᶜ≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
      ∀ ψ∈good n,FixedScoreAchievable CertificationGaussian.Consumers.actualPauliMUB.basis
        continuous_of_discreteTopology (uniformFiniteOutcome 3) 0 lam (radialSecondCoefficientSup 2 0 lam)
        (3/4) (1/4) (1/4) (spherePureVector ψ) ∧
        ENat.toENNReal (maximumBudget (spherePureVector ψ) (3/4) (1/4) (1/4))≤ENNReal.ofReal (K*Real.log 4) := by
  obtain ⟨lam,good,_h0,_ha,_hr,hcompact,hprob,hwindow⟩ :=
    completeMUB_corollary_three_six 2 0 (by norm_num) CertificationGaussian.Consumers.actualPauliMUB
  have hg : gamma ((2:ℝ)+1) 0<((3/4:ℝ)-1/4)/(1-1/4) := by
    rw [gamma_zero _ (by norm_num)]
    norm_num
  obtain ⟨K,hK,hN⟩ := hwindow (3/4) (1/4) (by norm_num) (by norm_num) (by norm_num) hg
  refine ⟨lam,good,K,hK,hcompact,?_⟩
  filter_upwards [hprob,hN] with n hn hrun
  refine ⟨hn,?_⟩
  intro ψ hψ
  have h := hrun ψ hψ (1/4) (by norm_num) (by norm_num)
  norm_num only [pow_zero,mul_one,one_div_div,div_one] at h
  exact h

end LocalCertification.Protocol.CompleteMUBConsumers
