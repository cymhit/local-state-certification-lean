import CertificationGaussian.ReadoutFullControl
import CertificationGaussian.Consumers.RadialReadoutPolar

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- Actual signed coefficients and the complete non-Hermitian phase family consume the final common Haar event for the full Pauli readout. -/
theorem signed_actual_full_readout_haar :
    ∃ C₁ C₂ CM : ℝ,0<C₁ ∧ 0<C₂ ∧ 0<CM ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      complexUnitaryHaar (QuditIndex 2 n) {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialReadoutFullBad 2 n 1 pauliBasisRecords pauliFullRecord signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) CM}≤
        ENNReal.ofReal ((radialHighGaussianConstant 2 1 signedHighRadialWeights+
          2*radialHighGaussianConstant 2 1 (fun j => (signedHighRadialWeights j)^2)+3)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex 2 n) U ψ∉
        radialReadoutFullBad 2 n 1 pauliBasisRecords pauliFullRecord signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) CM →
        radialReadoutFullControl 2 n 1 pauliBasisRecords pauliFullRecord signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) C₁ C₂ CM (complexUnitarySphereAction (QuditIndex 2 n) U ψ) := by
  obtain ⟨C₁,C₂,CM,h₁,h₂,hM,hE⟩ := radialPauli_full_readout_haar_eventually 1 signedHighRadialWeights
    (0:Fin 4) (by norm_num)
  refine ⟨C₁,C₂,CM,h₁,h₂,hM,?_⟩
  filter_upwards [hE] with n hn
  intro ψ
  exact (hn completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
    completePhaseBellFamily_hilbertSchmidt ψ).2

/-- The genuine full M and S integrals vanish at zero weights, even at n=0 or d=0. -/
theorem actual_full_second_zero_weights {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    cardinalityReadoutSecond d μ record r (fun _ => 0) ((d:ℝ)^n) ψ.ofLp=0 ∧
    cardinalityReadoutAuxiliary d μ record r (fun _ => 0) ((d:ℝ)^n) ψ.ofLp=0 ∧
    cardinalityReadoutSecondError d n r μ record (fun _ => 0) ψ=0 := by
  simp [cardinalityReadoutSecondError,cardinalityReadoutSecond,cardinalityReadoutAuxiliary,
    readoutSecondOperator,readoutAuxiliaryOperator,readoutCenteredScore,
    cardinalityReadoutKernel,finiteComplementKernel,cardinalityComplementWeight,
    cardinalityReadoutTraceScale,sphereQuadraticForm]

/-- A signed scalar radius regression retains the true h=1-2n and nu=1+4n, with explicit finite norm bounds 2 and 7. -/
theorem signed_full_second_scalar_regression (n : ℕ) (hn : 1≤n) :
    2*((n:ℝ)^5)⁻¹*7+4*((n:ℝ)^3)⁻¹+
      4*((n:ℝ)^5)⁻¹*|1-2*(n:ℝ)| *2+
      4*(((n:ℝ)^5)⁻¹)^2*(|1+4*(n:ℝ)|+(1-2*(n:ℝ))^2)≤98*((n:ℝ)^3)⁻¹ := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hh : |1-2*(n:ℝ)|≤3*(n:ℝ)^1 := by rw [abs_of_nonpos (by linarith),pow_one]; linarith
  have hnu : |1+4*(n:ℝ)|≤5*(n:ℝ)^1 := by rw [abs_of_nonneg (by linarith),pow_one]; linarith
  have h := readout_full_error_scalar_le n 1 hn 3 5 2 7 (1-2*n) (1+4*n)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh hnu
  norm_num only [show 1+4=5 by omega,show (2:ℝ)*7+4+4*3*2+4*(5+3^2)=98 by norm_num] at h
  exact h

end CertificationGaussian.Consumers
