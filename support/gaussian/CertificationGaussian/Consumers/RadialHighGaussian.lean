import CertificationGaussian.RadialHighTail
import CertificationGaussian.Consumers.RadialBellChoi

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- A fixed signed radial fixture: lambda0=1, lambda1=-2. -/
def signedHighRadialWeights (j : ℕ) : ℝ := if j=0 then 1 else -2

/-- Both actual high Gaussian blocks of the genuine complete phase-unitary fixture have the proved decay. -/
theorem signed_high_gaussian_expectations :
    ∀ᶠ n : ℕ in atTop,
      (∫ x,‖unitaryGaussianCentered
        (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (radialFirstHighWeights 2 1 signedHighRadialWeights (0:Fin 4)) x‖∂pairedGaussian (QuditIndex 2 n)) ≤
          radialHighGaussianConstant 2 1 signedHighRadialWeights*((n:ℝ)^11)⁻¹ ∧
      (∫ x,‖unitaryGaussianCentered
        (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (radialSecondHighWeights 2 1 signedHighRadialWeights (0:Fin 4)) x‖∂pairedGaussian (QuditIndex 2 n)) ≤
          (2*radialHighGaussianConstant 2 1 (fun j => (signedHighRadialWeights j)^2))*((n:ℝ)^11)⁻¹ := by
  filter_upwards [radialFirstHigh_gaussian_expectation 2 1 (by norm_num) signedHighRadialWeights
      (0:Fin 4) (by norm_num),
    radialSecondHigh_gaussian_expectation 2 1 (by norm_num) signedHighRadialWeights
      (0:Fin 4) (by norm_num)] with n h1 h2
  exact ⟨h1 completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
      completePhaseBellFamily_hilbertSchmidt,
    h2 completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
      completePhaseBellFamily_hilbertSchmidt⟩

/-- A genuine same-sample joint event for that non-individually-Hermitian signed fixture. -/
theorem signed_high_gaussian_joint_probability :
    ∀ᶠ n : ℕ in atTop,pairedGaussian (QuditIndex 2 n) {x |
      ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
        (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (radialFirstHighWeights 2 1 signedHighRadialWeights (0:Fin 4)) x‖ ∨
      ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
        (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (radialSecondHighWeights 2 1 signedHighRadialWeights (0:Fin 4)) x‖} ≤
      ENNReal.ofReal ((radialHighGaussianConstant 2 1 signedHighRadialWeights+
        2*radialHighGaussianConstant 2 1 (fun j => (signedHighRadialWeights j)^2))*((n:ℝ)^8)⁻¹) := by
  filter_upwards [radialHigh_gaussian_joint_tail 2 1 (by norm_num) signedHighRadialWeights
      (0:Fin 4) (by norm_num)] with n hn
  exact hn completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
    completePhaseBellFamily_hilbertSchmidt

/-- Zero weights annihilate the actual centered operator, including empty matrix dimensions. -/
theorem centered_zero_weights {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (W : K → Matrix I I ℂ) (x : Fin 2 × I → ℝ) : unitaryGaussianCentered W (fun _ => 0) x=0 := by
  simp [unitaryGaussianCentered,unitaryGaussianConjugation,unitaryWeightedRankOne,rectangularEuclideanCLM]

/-- Zero original coefficients annihilate both actual high blocks for every system size. -/
theorem radial_high_zero_coefficients {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (x : Fin 2 × QuditIndex d n → ℝ) :
    unitaryGaussianCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialFirstHighWeights d r (fun _ => 0) k0) x=0 ∧
    unitaryGaussianCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialSecondHighWeights d r (fun _ => 0) k0) x=0 := by
  have h1 : radialFirstHighWeights (S:=Fin n) d r (fun _ => 0) k0=(fun _ => 0) := by
    funext w
    simp [radialFirstHighWeights,radialFirstCoefficient]
  have h2 : radialSecondHighWeights (S:=Fin n) d r (fun _ => 0) k0=(fun _ => 0) := by
    funext w
    simp [radialSecondHighWeights,radialSecondCoefficient,radialFirstCoefficient]
  simp only [h1,h2,centered_zero_weights,and_self]

/-- With no sites both high blocks vanish, even d=0; the empty tensor still has one global coordinate. -/
theorem radial_high_empty_sites {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (x : Fin 2 × QuditIndex d 0 → ℝ) :
    unitaryGaussianCentered (fun w : Fin 0 → K => wickTensorMatrix (fun s => W (w s)))
      (radialFirstHighWeights d r lam k0) x=0 ∧
    unitaryGaussianCentered (fun w : Fin 0 → K => wickTensorMatrix (fun s => W (w s)))
      (radialSecondHighWeights d r lam k0) x=0 := by
  have h1 : radialFirstHighWeights (S:=Fin 0) d r lam k0=(fun _ => 0) := by
    funext w
    simp [radialFirstHighWeights,radialBellSupport]
  have h2 : radialSecondHighWeights (S:=Fin 0) d r lam k0=(fun _ => 0) := by
    funext w
    simp [radialSecondHighWeights,radialBellSupport]
  simp only [h1,h2,centered_zero_weights,and_self]

end CertificationGaussian.Consumers
