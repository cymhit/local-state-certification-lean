import CertificationGaussian.CompleteMUBFullControl
import CertificationGaussian.Consumers.CompleteMUB
import CertificationGaussian.Consumers.ReadoutFullControl

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- Actual signed weights and the existing complete phase-unitary family consume the genuine MUB full-readout Haar event. -/
theorem mub_signed_actual_full_readout_haar :
    ∃ C₁ C₂ CM : ℝ,0<C₁ ∧ 0<C₂ ∧ 0<CM ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      complexUnitaryHaar (QuditIndex 2 n) {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialReadoutFullBad 2 n 1 (completeMUBRecords 2) (completeMUBFullRecord actualPauliMUB) signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) CM}≤
        ENNReal.ofReal ((radialHighGaussianConstant 2 1 signedHighRadialWeights+
          2*radialHighGaussianConstant 2 1 (fun j => (signedHighRadialWeights j)^2)+3)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex 2 n) U ψ∉
        radialReadoutFullBad 2 n 1 (completeMUBRecords 2) (completeMUBFullRecord actualPauliMUB) signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) CM →
        radialReadoutFullControl 2 n 1 (completeMUBRecords 2) (completeMUBFullRecord actualPauliMUB) signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) C₁ C₂ CM (complexUnitarySphereAction (QuditIndex 2 n) U ψ) := by
  obtain ⟨C₁,C₂,CM,h₁,h₂,hM,hE⟩ := radialMUB_full_readout_haar_eventually 2 1 (by decide) actualPauliMUB signedHighRadialWeights
    (0:Fin 4) (by norm_num)
  refine ⟨C₁,C₂,CM,h₁,h₂,hM,?_⟩
  filter_upwards [hE] with n hn
  intro ψ
  exact (hn completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
    completePhaseBellFamily_hilbertSchmidt ψ).2


/-- The complete-MUB operator bounds specialize to the Pauli record model in dimension two. -/
theorem mub_actual_pauli_model (n r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    cardinalityReadoutSecond 2 (completeMUBRecords 2) (completeMUBFullRecord actualPauliMUB)
      r lam ((2:ℝ)^n) ψ.ofLp=
        cardinalityReadoutSecond 2 pauliBasisRecords pauliFullRecord r lam ((2:ℝ)^n) ψ.ofLp ∧
    cardinalityReadoutMean 2 (completeMUBRecords 2) (completeMUBFullRecord actualPauliMUB)
      r lam ((2:ℝ)^n) ψ.ofLp=
        cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam ((2:ℝ)^n) ψ.ofLp :=
  ⟨rfl,rfl⟩

/-- Genuine zero-weight M/S/full-error integrals retain the empty physical tensor and d=1 boundary. -/
theorem mub_one_dimensional_empty_zero
    (ψ : EuclideanSpace ℂ (QuditIndex 1 0)) :
    cardinalityReadoutSecond 1 (completeMUBRecords 1) (completeMUBFullRecord oneDimensionalMUB)
      0 (fun _ => 0) ((1:ℝ)^0) ψ.ofLp=0 ∧
    cardinalityReadoutAuxiliary 1 (completeMUBRecords 1) (completeMUBFullRecord oneDimensionalMUB)
      0 (fun _ => 0) ((1:ℝ)^0) ψ.ofLp=0 ∧
    cardinalityReadoutSecondError 1 0 0 (completeMUBRecords 1) (completeMUBFullRecord oneDimensionalMUB)
      (fun _ => 0) ψ=0 :=
  actual_full_second_zero_weights 1 0 0 (completeMUBRecords 1)
    (completeMUBFullRecord oneDimensionalMUB) ψ

end CertificationGaussian.Consumers
