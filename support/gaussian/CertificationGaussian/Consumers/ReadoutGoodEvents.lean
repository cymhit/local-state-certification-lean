import CertificationGaussian.ReadoutGoodEvents
import CertificationGaussian.Consumers.ReadoutRemainderTail

noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian.Consumers

/-- The actual signed Pauli remainder and common radius jointly consume an n^(-8) probability budget. -/
theorem actual_signed_joint_failure :
    ∀ᶠ n : ℕ in atTop,
      pairedGaussian (QuditIndex 2 n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord 2 signedPaperCoefficients (complexCoordinate x))‖ ∨
        ((n:ℝ)^6)⁻¹< |gaussianRadius (QuditIndex 2 n) x-1|} ≤
      ENNReal.ofReal (((n:ℝ)^8)⁻¹) :=
  cardinalityPauli_remainder_radius_inverse_power 2 8 signedPaperCoefficients

/-- For the actual qutrit Haar records, the threshold is uniform over every sufficiently large n at fixed r and coefficients. -/
theorem actual_qutrit_joint_failure (r : ℕ) (lam : ℕ → ℝ) :
    ∃ N : ℕ, 2≤N ∧ ∀ n : ℕ,N≤n →
      pairedGaussian (QuditIndex 3 n) {x |
        ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 3 n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) 3 (haarBasisRecords 3) id r lam (complexCoordinate x))‖ ∨
        ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 3 n) x-1|} ≤
      ENNReal.ofReal (((n:ℝ)^8)⁻¹) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (cardinalityHaar_remainder_radius_inverse_power 3 r 8 (by decide) lam)
  exact ⟨max N 2,le_max_right _ _,fun n hn => hN n ((le_max_left _ _).trans hn)⟩

/-- Empty output coordinates do not require the false identity norm(I)=1. -/
theorem actual_empty_second_error (nu h a : ℝ) :
    ‖Matrix.toEuclideanCLM (n:=Fin 0) (𝕜:=ℂ)
      ((0:Matrix (Fin 0) (Fin 0) ℂ)-nu • 1-0)‖≤|a-1|^2*(|nu|+h^2) := by
  have he : (0:Matrix (Fin 0) (Fin 0) ℂ)=nu • 1+a • 0+a^2 • 0+
      (2*(a-1)*h) • 0-((a-1)^2*(nu+h^2)) • 1 := Subsingleton.elim _ _
  simpa only [map_zero,norm_zero,mul_zero,add_zero,zero_add] using
    full_second_identity_error_bound (0:Matrix (Fin 0) (Fin 0) ℂ) 0 0 0 nu h a he

/-- A concrete two-qubit constant-shell consumer links the joint good event to the full second-moment error. -/
theorem actual_two_qubit_good_second (Kb Ks : ℝ) (x : Fin 2 × QuditIndex 2 2 → ℝ)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ (QuditIndex 2 2)) 1) :
    let ψ : QuditIndex 2 2 → ℂ := (sphereDirection e₀ (WithLp.toLp 2 (complexCoordinate x)) : EuclideanSpace ℂ (QuditIndex 2 2))
    let B := cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord 0 (fun _ => 1) 4 ψ
    let S := cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord 0 (fun _ => 1) 4 ψ
    let M := cardinalityReadoutSecond 2 pauliBasisRecords pauliFullRecord 0 (fun _ => 1) 4 ψ
    let Z := cardinalityReadoutRemainder 2 pauliBasisRecords pauliFullRecord 0 (fun _ => 1) (complexCoordinate x)
    ¬((1/8:ℝ)<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 2) (𝕜:=ℂ) Z‖ ∨
      (1/16:ℝ)< |gaussianRadius (QuditIndex 2 2) x-1|) →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 2) (𝕜:=ℂ) B‖≤Kb →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 2) (𝕜:=ℂ) S‖≤Ks →
    ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 2) (𝕜:=ℂ) (M-1-S)‖≤Ks/8+1/2+Kb/4+1/32 := by
  dsimp only
  intro hgood hB hS
  have hrad : |gaussianRadius (QuditIndex 2 2) x-1|≤(1/16:ℝ) :=
    le_of_not_gt (fun h => hgood (Or.inr h))
  have hZ : ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 2) (𝕜:=ℂ)
      (cardinalityReadoutRemainder 2 pauliBasisRecords pauliFullRecord 0 (fun _ => 1) (complexCoordinate x))‖≤(1/8:ℝ) :=
    le_of_not_gt (fun h => hgood (Or.inl h))
  have hh := cardinalityPauli_second_error_of_good_radius 2 0 (by decide) (fun _ => 1) Kb Ks x e₀
    (by norm_num; exact hrad)
  norm_num [cardinalityReadoutTraceScale] at hh
  have h := hh hZ hB hS
  simp only [map_sub,map_one]
  convert h using 1
  ring

end CertificationGaussian.Consumers
