import CertificationGaussian.RadialLinearLowOrbit
import CertificationGaussian.RadialLinearHighTail
import CertificationGaussian.Consumers.RadialHighGaussian

noncomputable section
open MeasureTheory Matrix Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- The same signed complete family containing iX has actual exponential high and low events at one fixed entropy-gap cutoff. -/
theorem signed_linear_high_low_exponential :
    ∃ ε cH cL : ℝ,0<ε ∧ ε<1/2 ∧ 0<cH ∧ 0<cL ∧
      (∀ᶠ n : ℕ in atTop,pairedGaussian (QuditIndex 2 n) {x |
        ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
          (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
          (radialLinearFirstHighWeights 2 n 1 ε signedHighRadialWeights (0:Fin 4)) x‖ ∨
        ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
          (fun w : Fin n → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
          (radialLinearSecondHighWeights 2 n 1 ε signedHighRadialWeights (0:Fin 4)) x‖}≤
        ENNReal.ofReal (2*Real.exp (-cH*n))) ∧
      (∀ᶠ n : ℕ in atTop,∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
        complexUnitaryHaar (QuditIndex 2 n) {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
          radialLinearLowSphereBad 2 n ε completePhaseBellFamily (0:Fin 4)}≤
            ENNReal.ofReal (Real.exp (-cL*n))) := by
  obtain ⟨ε,hε,hhalf,hgap⟩ := exists_radialLinearEntropy_gap 2 (by norm_num)
  have hr := radialLinearHighRate_pos 2 (by norm_num) ε hε hgap
  refine ⟨ε,radialLinearHighRate 2 ε/4,(Real.log (2:ℝ)-2*radialLinearEntropy 2 ε)/2,
    hε,hhalf,by linarith,by linarith,?_,?_⟩
  · filter_upwards [radialLinearHigh_gaussian_joint_tail 2 1 (by norm_num) ε hε hhalf hgap
      signedHighRadialWeights (0:Fin 4) (by norm_num)] with n hn
    exact hn completePhaseBellFamily completePhaseBellFamily_identity completePhaseBellFamily_unitary
      completePhaseBellFamily_hilbertSchmidt
  · filter_upwards [radialLinearLow_haar_tail 2 (by norm_num) ε hε hhalf (0:Fin 4) (by norm_num) hgap] with n hn
    exact hn completePhaseBellFamily completePhaseBellFamily_unitary completePhaseBellFamily_hilbertSchmidt

/-- No sites gives exactly one low word for every cutoff, independently of the local label cardinality. -/
theorem linear_low_empty_sites {K : Type*} [Fintype K] [DecidableEq K] (ε : ℝ) (k0 : K) :
    (radialLinearLowLabels ε 0 k0).card=1 := by
  simp [radialLinearLowLabels_card,radialLinearWeightCutoff]

/-- A concrete linear ball count uses the real support and the floor cutoff, not an asymptotic surrogate. -/
theorem linear_low_eight_sites :
    (radialLinearLowLabels (1/4:ℝ) 8 (0:Fin 4)).card=277 := by
  norm_num [radialLinearLowLabels_card,radialLinearWeightCutoff,Finset.sum_range_succ,Nat.choose]

/-- Zero original weights annihilate both actual centered linear high blocks, including empty matrix dimensions. -/
theorem linear_high_zero_coefficients {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (x : Fin 2 × QuditIndex d n → ℝ) :
    unitaryGaussianCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearFirstHighWeights d n r ε (fun _ => 0) k0) x=0 ∧
    unitaryGaussianCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearSecondHighWeights d n r ε (fun _ => 0) k0) x=0 := by
  have h1 : radialLinearFirstHighWeights d n r ε (fun _ => 0) k0=(fun _ => 0) := by
    funext w
    simp [radialLinearFirstHighWeights,radialFirstCoefficient]
  have h2 : radialLinearSecondHighWeights d n r ε (fun _ => 0) k0=(fun _ => 0) := by
    funext w
    simp [radialLinearSecondHighWeights,radialSecondCoefficient,radialFirstCoefficient]
  simp only [h1,h2,centered_zero_weights,and_self]

/-- The empty tensor still has one global coordinate; both high blocks vanish even when d=0. -/
theorem linear_high_empty_sites {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (x : Fin 2 × QuditIndex d 0 → ℝ) :
    unitaryGaussianCentered (fun w : Fin 0 → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearFirstHighWeights d 0 r ε lam k0) x=0 ∧
    unitaryGaussianCentered (fun w : Fin 0 → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearSecondHighWeights d 0 r ε lam k0) x=0 := by
  have h1 : radialLinearFirstHighWeights d 0 r ε lam k0=(fun _ => 0) := by
    funext w
    simp [radialLinearFirstHighWeights,radialBellSupport]
  have h2 : radialLinearSecondHighWeights d 0 r ε lam k0=(fun _ => 0) := by
    funext w
    simp [radialLinearSecondHighWeights,radialBellSupport]
  simp only [h1,h2,centered_zero_weights,and_self]

end CertificationGaussian.Consumers
