import CertificationGaussian.RadialReadoutPolar
import CertificationGaussian.Consumers.ReadoutRadialSpectrum

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- The signed complete family containing iX has genuine Haar-state probability and actual finite-Pauli B/S polar control. -/
theorem signed_readout_polar_haar :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      complexUnitaryHaar (QuditIndex 2 n) {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialHighSphereBad 2 n 1 signedHighRadialWeights completePhaseBellFamily (0:Fin 4) ∪
          radialLowSphereBad 2 n 1 completePhaseBellFamily (0:Fin 4)}≤
        ENNReal.ofReal ((radialHighGaussianConstant 2 1 signedHighRadialWeights+
          2*radialHighGaussianConstant 2 1 (fun j => (signedHighRadialWeights j)^2)+2)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex 2 n) U ψ∉
        radialHighSphereBad 2 n 1 signedHighRadialWeights completePhaseBellFamily (0:Fin 4) ∪
          radialLowSphereBad 2 n 1 completePhaseBellFamily (0:Fin 4) →
        radialReadoutPolarControl 2 n 1 pauliBasisRecords pauliFullRecord signedHighRadialWeights
          completePhaseBellFamily (0:Fin 4) C₁ C₂ (complexUnitarySphereAction (QuditIndex 2 n) U ψ) := by
  obtain ⟨C₁,C₂,h₁,h₂,hE⟩ := radialPauliReadoutPolar_haar_eventually 1 signedHighRadialWeights
    (0:Fin 4) (by norm_num)
  refine ⟨C₁,C₂,h₁,h₂,?_⟩
  filter_upwards [hE] with n hn
  intro ψ
  exact (hn completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
    completePhaseBellFamily_hilbertSchmidt ψ).2

/-- The original signed first diagonal really has a negative nonidentity coefficient; the second uses squared lambda. -/
theorem signed_original_low_diagonal :
    radialFirstCoefficient 2 1 signedHighRadialWeights 0=1 ∧
    radialFirstCoefficient 2 1 signedHighRadialWeights 1= -1 ∧
    radialSecondCoefficient 2 1 signedHighRadialWeights 0=2 ∧
    radialSecondCoefficient 2 1 signedHighRadialWeights 1=6 := by
  norm_num [radialFirstCoefficient,radialSecondCoefficient,signedHighRadialWeights,
    Fin.sum_univ_succ,Nat.choose]

/-- Zero diagonal weights give zero actual CFC compression for every site count and local dimension. -/
theorem radial_polar_zero_weights {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    radialPolarCompression d n r W k0 (fun _ => 0) ψ=0 := by
  simp [radialPolarCompression,rectangularEuclideanCLM]

/-- With no sites the actual low tensor orbit is the identity, including local dimension zero. -/
theorem no_sites_low_orbit {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (w : radialLowLabels (S:=Fin 0) d r k0) :
    radialLowOrbitFamily d 0 r W k0 w=1 := by
  ext i j
  have hij : i=j := Subsingleton.elim _ _
  simp [radialLowOrbitFamily,wickTensorMatrix,Matrix.one_apply,hij]

end CertificationGaussian.Consumers
