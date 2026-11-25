import CertificationGaussian.RadialHighSphere
import CertificationGaussian.Consumers.RadialHighGaussian

noncomputable section
open MeasureTheory Matrix Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- The complementary coefficient is 3 for the signed weights and 5 for their squares. -/
theorem signed_high_sphere_constants :
    complementLambdaCoefficient 2 1 signedHighRadialWeights=3 ∧
    complementLambdaCoefficient 2 1 (fun j => (signedHighRadialWeights j)^2)=5 := by
  norm_num [complementLambdaCoefficient,Fin.sum_univ_succ,signedHighRadialWeights]

/-- A canonical-sphere event for the actual complete phase-unitary family, including iX. -/
theorem signed_high_sphere_joint_probability :
    ∀ᶠ n : ℕ in atTop,canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 n))
      {ψ | (8:ℝ)*((n:ℝ)^3)⁻¹<‖unitarySphereCentered
        (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (radialFirstHighWeights 2 1 signedHighRadialWeights (0:Fin 4)) ψ‖ ∨
        (22:ℝ)*((n:ℝ)^3)⁻¹<‖unitarySphereCentered
        (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (radialSecondHighWeights 2 1 signedHighRadialWeights (0:Fin 4)) ψ‖} ≤
      ENNReal.ofReal ((radialHighGaussianConstant 2 1 signedHighRadialWeights+
        2*radialHighGaussianConstant 2 1 (fun j => (signedHighRadialWeights j)^2)+1)*((n:ℝ)^8)⁻¹) := by
  filter_upwards [radialHigh_canonicalSphere_joint_tail 2 1 (by norm_num) signedHighRadialWeights
    (0:Fin 4) (by norm_num)] with n hn
  have h := hn completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
    completePhaseBellFamily_hilbertSchmidt
  simpa only [radialHighSphereBad,signed_high_sphere_constants.1,signed_high_sphere_constants.2,
    show (2:ℝ)+2*3=8 by norm_num,show (2:ℝ)+4*5=22 by norm_num] using h

/-- The cutoff precedes every initial vector in the genuine full-unitary Haar orbit law. -/
theorem signed_high_haar_joint_probability :
    ∀ᶠ n : ℕ in atTop,∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      complexUnitaryHaar (QuditIndex 2 n)
        {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
          radialHighSphereBad 2 n 1 signedHighRadialWeights completePhaseBellFamily (0:Fin 4)} ≤
      ENNReal.ofReal ((radialHighGaussianConstant 2 1 signedHighRadialWeights+
        2*radialHighGaussianConstant 2 1 (fun j => (signedHighRadialWeights j)^2)+1)*((n:ℝ)^8)⁻¹) := by
  filter_upwards [radialHigh_haar_joint_tail 2 1 (by norm_num) signedHighRadialWeights
    (0:Fin 4) (by norm_num)] with n hn
  exact hn completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
    completePhaseBellFamily_hilbertSchmidt

/-- The sphere operator is the weighted sum of the conjugates of the outer product of ψ with itself. -/
theorem sphere_operator_actual_sum {I K : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype K] (W : K → Matrix I I ℂ) (a : K → ℝ) (ψ : EuclideanSpace ℂ I) :
    unitarySphereConjugation W a ψ=rectangularEuclideanCLM
      (∑ w,(a w:ℂ) • (W w*Matrix.vecMulVec ψ.ofLp (fun i => star (ψ.ofLp i))*(W w)ᴴ)) :=
  unitarySphereConjugation_eq_sum W a ψ

/-- Zero weights give zero actual centered sphere operator, including empty matrix indices. -/
theorem sphere_centered_zero_weights {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (W : K → Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) :
    unitarySphereCentered W (fun _ => 0) ψ=0 := by
  simp [unitarySphereCentered,unitarySphereConjugation,unitaryWeightedRankOne,rectangularEuclideanCLM]

/-- With no sites the two actual high operators are zero, even for local dimension zero. -/
theorem sphere_high_empty_sites {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (ψ : EuclideanSpace ℂ (QuditIndex d 0)) :
    unitarySphereCentered (fun w : Fin 0 → K => wickTensorMatrix (fun s => W (w s)))
      (radialFirstHighWeights d r lam k0) ψ=0 ∧
    unitarySphereCentered (fun w : Fin 0 → K => wickTensorMatrix (fun s => W (w s)))
      (radialSecondHighWeights d r lam k0) ψ=0 := by
  have h1 : radialFirstHighWeights (S:=Fin 0) d r lam k0=(fun _ => 0) := by
    funext w
    simp [radialFirstHighWeights,radialBellSupport]
  have h2 : radialSecondHighWeights (S:=Fin 0) d r lam k0=(fun _ => 0) := by
    funext w
    simp [radialSecondHighWeights,radialBellSupport]
  simp only [h1,h2,sphere_centered_zero_weights,and_self]

end CertificationGaussian.Consumers
