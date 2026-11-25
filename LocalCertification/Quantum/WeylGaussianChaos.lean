import LocalCertification.Quantum.WeylTensor
import CertificationGaussian.Consumers.UnitaryGaussianChaos

set_option autoImplicit false
open MeasureTheory Matrix CertificationGaussian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

/-- The actual canonical tensor Weyl family is unitary, including composite local dimensions and n=0. -/
theorem quditWeyl_unitary (u : WeylLabel d n) :
    quditWeyl u ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :=
  ⟨quditWeyl_adjoint_mul u, quditWeyl_mul_adjoint u⟩

/-- Exact Hilbert-Schmidt normalization for the sole physical qudit index. -/
theorem quditWeyl_hilbertSchmidt_card (u v : WeylLabel d n) :
    ((quditWeyl u)ᴴ * quditWeyl v).trace =
      if u=v then (Fintype.card (QuditIndex d n) : ℂ) else 0 := by
  simpa only [qudit_card, Nat.cast_pow] using quditWeyl_hilbertSchmidt u v

/-- This is the existing CN(0,1) model, with the literal Weyl-conjugated rank-one matrix and factor 1/d^n. -/
theorem quditWeyl_gaussian_actual (a : WeylLabel d n → ℝ)
    (g : Fin 2 × QuditIndex d n → ℝ) :
    unitaryGaussianConjugation quditWeyl a g =
      rectangularEuclideanCLM (((d:ℂ)^n)⁻¹ • ∑ u, (a u:ℂ) •
        (quditWeyl u * Matrix.vecMulVec (complexCoordinate g) (fun j => star (complexCoordinate g j)) *
          (quditWeyl u)ᴴ)) := by
  simp only [unitaryGaussianConjugation, unitaryWeightedRankOne, qudit_card, Nat.cast_pow]

theorem quditWeyl_gaussian_integrable (a : WeylLabel d n → ℝ) :
    Integrable (unitaryGaussianConjugation quditWeyl a) (pairedGaussian (QuditIndex d n)) :=
  unitaryGaussianConjugation_integrable quditWeyl a

/-- The exact Bochner mean for arbitrary real signed weights. -/
theorem quditWeyl_gaussian_mean (a : WeylLabel d n → ℝ) :
    (∫ g, unitaryGaussianConjugation quditWeyl a g ∂pairedGaussian (QuditIndex d n)) =
      rectangularEuclideanCLM (((∑ u, (a u:ℂ))/(d:ℂ)^n) • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) := by
  simpa only [qudit_card, Nat.cast_pow] using
    unitaryGaussianConjugation_mean quditWeyl a quditWeyl_unitary

/-- The first two actual rectangular flattenings have the same exact square-sum control. -/
theorem quditWeyl_gaussian_first_two_controls (a : WeylLabel d n → ℝ) :
    ‖rectangularEuclideanCLM (chaosFlattening₁ (unitaryChaosCoefficient quditWeyl a))‖ =
      Real.sqrt ((∑ u, (a u)^2)/(d:ℝ)^n) ∧
    ‖rectangularEuclideanCLM (chaosFlattening₂ (unitaryChaosCoefficient quditWeyl a))‖ =
      Real.sqrt ((∑ u, (a u)^2)/(d:ℝ)^n) := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  constructor
  · simpa only [unitaryWeightSquareMean, qudit_card, Nat.cast_pow] using
      chaosFlattening₁_unitary_norm quditWeyl a quditWeyl_unitary quditWeyl_hilbertSchmidt_card
  · simpa only [unitaryWeightSquareMean, qudit_card, Nat.cast_pow] using
      chaosFlattening₂_unitary_norm quditWeyl a quditWeyl_unitary quditWeyl_hilbertSchmidt_card

/-- Bell diagonalization keeps the actual canonical Weyl vectors; the exact norm is the signed-weight sup norm. -/
theorem quditWeyl_gaussian_bell_norm (a : WeylLabel d n → ℝ) :
    ‖rectangularEuclideanCLM (weightedBellMatrix quditWeyl a)‖ = ‖a‖ :=
  weightedBellMatrix_norm quditWeyl a quditWeyl_hilbertSchmidt_card

/-- All four genuine flattenings reduce to these three controls for the actual Weyl family. -/
theorem quditWeyl_gaussian_three_controls (a : WeylLabel d n → ℝ) :
    gaussianChaosFlatteningNorm (unitaryChaosCoefficient quditWeyl a) =
      max (Real.sqrt ((∑ u, (a u)^2)/(d:ℝ)^n))
        (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix quditWeyl a))‖) := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  simpa only [unitaryWeightSquareMean, qudit_card, Nat.cast_pow] using
    unitaryChaosCoefficient_flatteningNorm quditWeyl a quditWeyl_unitary quditWeyl_hilbertSchmidt_card

/-- Actual centered Weyl-Gaussian operator-norm expectation, with one logarithm and an absolute constant. -/
theorem quditWeyl_gaussian_expectation (a : WeylLabel d n → ℝ) :
    (∫ g, ‖unitaryGaussianConjugation quditWeyl a g -
      rectangularEuclideanCLM (((∑ u, (a u:ℂ))/(d:ℂ)^n) • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ))‖
      ∂pairedGaussian (QuditIndex d n)) ≤
      (8*gaussianMatrixChaosConstant) * Real.log (2*(d:ℝ)^n) *
        max (Real.sqrt ((∑ u, (a u)^2)/(d:ℝ)^n))
          (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix quditWeyl a))‖) := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  simpa only [unitaryWeightSquareMean, qudit_card, Nat.cast_pow] using
    unitaryGaussianConjugation_expectation_bound quditWeyl a quditWeyl_unitary quditWeyl_hilbertSchmidt_card

end LocalCertification.Quantum
