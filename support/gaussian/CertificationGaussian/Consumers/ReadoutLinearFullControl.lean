import CertificationGaussian.ReadoutLinearFullControl
import CertificationGaussian.Consumers.ReadoutFullControl

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- The actual signed phase-unitary example admits one fixed linear cutoff and a genuine exponential full-M Haar event. -/
theorem signed_actual_full_readout_exponential :
    ∃ ε c C₁ C₂ CM : ℝ,0<ε ∧ ε<1/2 ∧ radialLinearEntropy 2 ε<Real.log (2:ℝ)/2 ∧
      0<c ∧ 0<C₁ ∧ 0<C₂ ∧ 0<CM ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      complexUnitaryHaar (QuditIndex 2 n) {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialLinearReadoutFullBad 2 n 1 ε pauliBasisRecords pauliFullRecord signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) CM}≤ENNReal.ofReal (Real.exp (-c*n)) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex 2 n) U ψ∉
        radialLinearReadoutFullBad 2 n 1 ε pauliBasisRecords pauliFullRecord signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) CM →
        radialLinearReadoutFullControl 2 n 1 ε pauliBasisRecords pauliFullRecord signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) C₁ C₂ CM (complexUnitarySphereAction (QuditIndex 2 n) U ψ) := by
  obtain ⟨ε,c,C₁,C₂,CM,hε,hhalf,hgap,hc,h₁,h₂,hM,hE⟩ := radialPauli_readout_exponential 1 signedHighRadialWeights
    (0:Fin 4) (by norm_num)
  refine ⟨ε,c,C₁,C₂,CM,hε,hhalf,hgap,hc,h₁,h₂,hM,?_⟩
  filter_upwards [hE] with n hn
  intro ψ
  exact (hn completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
    completePhaseBellFamily_hilbertSchmidt ψ).2

/-- Identically zero weights give zero linear-cutoff compression in every dimension. -/
theorem linear_polar_zero_weights {K : Type*} [Fintype K] [DecidableEq K]
    (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    radialLinearPolarCompression d n ε W k0 (fun _ => 0) ψ=0 := by
  simp [radialLinearPolarCompression,rectangularEuclideanCLM]

/-- With no sites the actual linear low orbit is the identity, even at local dimension zero. -/
theorem linear_no_sites_low_orbit {K : Type*} [Fintype K] [DecidableEq K]
    (d : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (w : radialLinearLowLabels ε 0 k0) :
    radialLinearLowOrbitFamily d 0 ε W k0 w=1 := by
  ext i j
  have hij : i=j := Subsingleton.elim _ _
  simp [radialLinearLowOrbitFamily,wickTensorMatrix,Matrix.one_apply,hij]

/-- The unmodified actual M and S integrals are still zero for zero coefficients; the new cutoff does not redefine them. -/
theorem linear_actual_full_second_zero {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    cardinalityReadoutSecond d μ record r (fun _ => 0) ((d:ℝ)^n) ψ.ofLp=0 ∧
    cardinalityReadoutAuxiliary d μ record r (fun _ => 0) ((d:ℝ)^n) ψ.ofLp=0 ∧
    cardinalityReadoutSecondError d n r μ record (fun _ => 0) ψ=0 :=
  actual_full_second_zero_weights d n r μ record ψ

end CertificationGaussian.Consumers
