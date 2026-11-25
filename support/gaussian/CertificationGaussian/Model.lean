/-
Quartic polynomial model for a fixed matrix or basis parameter and a signed kernel.
This module expresses normalized complex coordinates and matrix outcomes
as real polynomials, then proves the evaluation identities and degree-four bound.
This layer contains no hypercontractive bound.
-/
import CertificationGaussian.Coordinates
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.MvPolynomial.CommRing

/- The unnormalized Q_U - v, with arbitrary fixed matrix/basis parameter
and arbitrary real signed kernel. No Gaussian mean/variance or Haar result is claimed. -/
noncomputable section
open MeasureTheory GaussianHilbert MvPolynomial
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I]

def complexCoordinate (x : (Fin 2 × I) → ℝ) (j : I) : ℂ :=
  ((x (0,j) / Real.sqrt 2 : ℝ) : ℂ) + ((x (1,j) / Real.sqrt 2 : ℝ) : ℂ) * Complex.I

omit [Fintype I] in
theorem complexCoordinate_normalization (x : (Fin 2 × I) → ℝ) (j : I) :
    complexCoordinate x j = ((x (0,j) : ℂ) + Complex.I * (x (1,j) : ℂ)) / (Real.sqrt 2 : ℂ) := by
  simp only [complexCoordinate, Complex.ofReal_div]
  ring

def realLinearPoly (A : Matrix I I ℂ) (i : I) : MvPolynomial (Fin 2 × I) ℝ :=
  ∑ j, (C ((A i j).re / Real.sqrt 2) * X (0,j) - C ((A i j).im / Real.sqrt 2) * X (1,j))

def imagLinearPoly (A : Matrix I I ℂ) (i : I) : MvPolynomial (Fin 2 × I) ℝ :=
  ∑ j, (C ((A i j).re / Real.sqrt 2) * X (1,j) + C ((A i j).im / Real.sqrt 2) * X (0,j))

theorem eval_realLinear (A : Matrix I I ℂ) (i : I) (x : (Fin 2 × I) → ℝ) :
    eval x (realLinearPoly A i) = (A.mulVec (complexCoordinate x) i).re := by
  simp only [realLinearPoly, map_sum, map_sub, map_mul, eval_C, eval_X,
    Matrix.mulVec, dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [complexCoordinate, Complex.mul_re]
  ring

theorem eval_imagLinear (A : Matrix I I ℂ) (i : I) (x : (Fin 2 × I) → ℝ) :
    eval x (imagLinearPoly A i) = (A.mulVec (complexCoordinate x) i).im := by
  simp only [imagLinearPoly, map_sum, map_add, map_mul, eval_C, eval_X,
    Matrix.mulVec, dotProduct, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [complexCoordinate, Complex.mul_im]
  ring

def outcomePoly (A : Matrix I I ℂ) (i : I) : MvPolynomial (Fin 2 × I) ℝ :=
  realLinearPoly A i ^ 2 + imagLinearPoly A i ^ 2 - C 1

def gaussianOutcome (A : Matrix I I ℂ) (x : (Fin 2 × I) → ℝ) (i : I) : ℝ :=
  Complex.normSq (A.mulVec (complexCoordinate x) i) - 1

theorem eval_outcome (A : Matrix I I ℂ) (i : I) (x : (Fin 2 × I) → ℝ) :
    eval x (outcomePoly A i) = gaussianOutcome A x i := by
  simp only [outcomePoly, map_sub, map_add, map_mul, eval_C, eval_realLinear, eval_imagLinear,
    gaussianOutcome, Complex.normSq_apply, pow_two]

def quarticPoly (U : Matrix I I ℂ) (R : Matrix I I ℝ) (v : ℝ) : MvPolynomial (Fin 2 × I) ℝ :=
  C ((Fintype.card I : ℝ)⁻¹) *
    (∑ i, ∑ j, C ((R*R) i j) * outcomePoly U.conjTranspose i * outcomePoly U.conjTranspose j) - C v

def gaussianQuartic (U : Matrix I I ℂ) (R : Matrix I I ℝ) (v : ℝ)
    (x : (Fin 2 × I) → ℝ) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ *
    (∑ i, ∑ j, (R*R) i j * gaussianOutcome U.conjTranspose x i * gaussianOutcome U.conjTranspose x j) - v

theorem eval_quartic (U : Matrix I I ℂ) (R : Matrix I I ℝ) (v : ℝ) (x : (Fin 2 × I) → ℝ) :
    eval x (quarticPoly U R v) = gaussianQuartic U R v x := by
  simp [quarticPoly, gaussianQuartic, eval_outcome]

theorem degree_C_mul {J : Type*} (c : ℝ) (P : MvPolynomial J ℝ) :
    (C c * P).totalDegree ≤ P.totalDegree := by
  simpa using totalDegree_mul (C c) P

theorem degree_realLinear (A : Matrix I I ℂ) (i : I) : (realLinearPoly A i).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j hj
  apply (totalDegree_sub _ _).trans
  exact max_le ((degree_C_mul _ _).trans (by simp)) ((degree_C_mul _ _).trans (by simp))

theorem degree_imagLinear (A : Matrix I I ℂ) (i : I) : (imagLinearPoly A i).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j hj
  apply (totalDegree_add _ _).trans
  exact max_le ((degree_C_mul _ _).trans (by simp)) ((degree_C_mul _ _).trans (by simp))

theorem degree_outcome (A : Matrix I I ℂ) (i : I) : (outcomePoly A i).totalDegree ≤ 2 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (degree_realLinear A i))
  · exact (totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (degree_imagLinear A i))

theorem degree_quartic (U : Matrix I I ℂ) (R : Matrix I I ℝ) (v : ℝ) :
    (quarticPoly U R v).totalDegree ≤ 4 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply (degree_C_mul _ _).trans
  apply totalDegree_finsetSum_le
  intro i hi
  apply totalDegree_finsetSum_le
  intro j hj
  apply (totalDegree_mul _ _).trans
  exact Nat.add_le_add ((degree_C_mul _ _).trans (degree_outcome _ i)) (degree_outcome _ j)

abbrev QuditIndex (d n : Nat) := Fin n → Fin d

theorem qudit_card (d n : Nat) : Fintype.card (QuditIndex d n) = d^n := by simp [QuditIndex]

def hammingDistance {d n : Nat} (x y : QuditIndex d n) : Nat :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

def distanceAverage (d n k : Nat) : Matrix (QuditIndex d n) (QuditIndex d n) ℝ := fun x y =>
  if hammingDistance x y = k then ((Nat.choose n k : ℝ) * ((d-1 : Nat) : ℝ)^k)⁻¹ else 0

def signedHammingKernel (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ) :
    Matrix (QuditIndex d n) (QuditIndex d n) ℝ := ∑ k ∈ J, θ k • distanceAverage d n k

def kernelVarianceScale (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ) : ℝ :=
  ∑ k ∈ J, (θ k)^2 / ((Nat.choose n k : ℝ) * ((d-1 : Nat) : ℝ)^k)

def quditQuartic (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :=
  gaussianQuartic U (signedHammingKernel d n J θ) (kernelVarianceScale d n J θ)

/- The exact 2*d^n standard-real-coordinate interface used by the paper. -/
def quditCoordIndex (d n : Nat) : Fin (2*d^n) ≃ Fin 2 × QuditIndex d n :=
  (Fintype.equivFinOfCardEq (α := Fin 2 × QuditIndex d n) (by simp)).symm

def quditCoordinates (d n : Nat) : (Fin (2*d^n) → ℝ) ≃ᵐ ((Fin 2 × QuditIndex d n) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × QuditIndex d n => ℝ) (quditCoordIndex d n)

theorem qudit_coordinate_preserving (d n : Nat) : MeasurePreserving (quditCoordinates d n)
    (stdGaussianFin (2*d^n)) (pairedGaussian (QuditIndex d n)) := by
  simpa [quditCoordinates, stdGaussianFin, pairedGaussian] using
    measurePreserving_piCongrLeft
      (fun _ : Fin 2 × QuditIndex d n => ProbabilityTheory.gaussianReal 0 1) (quditCoordIndex d n)

theorem qudit_coordinate_apply (d n : Nat) (x : Fin (2*d^n) → ℝ) (c : Fin 2 × QuditIndex d n) :
    quditCoordinates d n x c = x ((quditCoordIndex d n).symm c) := by
  simpa [quditCoordinates] using MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin 2 × QuditIndex d n => ℝ) (quditCoordIndex d n) x ((quditCoordIndex d n).symm c)

def quditPolynomial (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) : MvPolynomial (Fin (2*d^n)) ℝ :=
  rename (quditCoordIndex d n).symm
    (quarticPoly U (signedHammingKernel d n J θ) (kernelVarianceScale d n J θ))

def quditStandardQuartic (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) : (Fin (2*d^n) → ℝ) → ℝ :=
  quditQuartic d n J θ U ∘ quditCoordinates d n

theorem eval_quditPolynomial (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) (x : Fin (2*d^n) → ℝ) :
    eval x (quditPolynomial d n J θ U) = quditStandardQuartic d n J θ U x := by
  simp only [quditPolynomial, eval_rename]
  have he : x ∘ (quditCoordIndex d n).symm = quditCoordinates d n x := by
    funext c
    exact (qudit_coordinate_apply d n x c).symm
  rw [he, eval_quartic]
  rfl

theorem degree_quditPolynomial (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :
    (quditPolynomial d n J θ U).totalDegree ≤ 4 :=
  (totalDegree_rename_le _ _).trans (degree_quartic _ _ _)

theorem quditStandardQuartic_measurable (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) : Measurable (quditStandardQuartic d n J θ U) := by
  simpa only [eval_quditPolynomial] using (quditPolynomial d n J θ U).continuous_eval.measurable

theorem qudit_eLpNorm_transport (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) (p : ENNReal) :
    eLpNorm (quditStandardQuartic d n J θ U) p (stdGaussianFin (2*d^n)) =
      eLpNorm (quditQuartic d n J θ U) p (pairedGaussian (QuditIndex d n)) := by
  have h := (quditCoordinates d n).measurableEmbedding.eLpNorm_map_measure
    (μ := stdGaussianFin (2*d^n)) (g := quditQuartic d n J θ U) (p := p)
  rw [(qudit_coordinate_preserving d n).map_eq] at h
  exact h.symm

theorem gaussianQuartic_formula (U : Matrix I I ℂ) (R : Matrix I I ℝ) (v : ℝ)
    (x : (Fin 2 × I) → ℝ) : gaussianQuartic U R v x =
      (1 / (Fintype.card I : ℝ)) * (∑ i, ∑ j, (R*R) i j *
        (‖U.conjTranspose.mulVec (complexCoordinate x) i‖^2-1) *
        (‖U.conjTranspose.mulVec (complexCoordinate x) j‖^2-1)) - v := by
  simp only [gaussianQuartic, gaussianOutcome, Complex.normSq_eq_norm_sq, one_div]

end CertificationGaussian
