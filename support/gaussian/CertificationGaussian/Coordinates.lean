/-
Real and complex Gaussian coordinate representations for the quartic model.
This module reindexes standard real Gaussian coordinates into pairs and
proves the corresponding measure-preservation and polynomial-evaluation identities.
This layer contains no hypercontractive bound.
-/
import CertificationGaussian.StandardGaussian
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open MeasureTheory GaussianHilbert
namespace CertificationGaussian

variable (I : Type*) [Fintype I]

def coordIndex : Fin (2 * Fintype.card I) ≃ Fin 2 × I :=
  (Fintype.equivFinOfCardEq (α := Fin 2 × I) (by simp)).symm

def coordEquiv : (Fin (2 * Fintype.card I) → ℝ) ≃ᵐ ((Fin 2 × I) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × I => ℝ) (coordIndex I)

def pairedGaussian : Measure ((Fin 2 × I) → ℝ) :=
  Measure.pi (fun _ : Fin 2 × I => ProbabilityTheory.gaussianReal 0 1)

theorem coord_preserving : MeasurePreserving (coordEquiv I)
    (stdGaussianFin (2 * Fintype.card I)) (pairedGaussian I) := by
  simpa [coordEquiv, stdGaussianFin, pairedGaussian] using
    (measurePreserving_piCongrLeft
      (fun _ : Fin 2 × I => ProbabilityTheory.gaussianReal 0 1) (coordIndex I))

theorem coord_apply (x : Fin (2 * Fintype.card I) → ℝ) (c : Fin 2 × I) :
    coordEquiv I x c = x ((coordIndex I).symm c) := by
  simpa [coordEquiv] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 2 × I => ℝ) (coordIndex I) x ((coordIndex I).symm c)

theorem coord_eLpNorm (f : ((Fin 2 × I) → ℝ) → ℝ) (p : ENNReal) :
    eLpNorm (f ∘ coordEquiv I) p (stdGaussianFin (2 * Fintype.card I)) =
      eLpNorm f p (pairedGaussian I) := by
  have h := (coordEquiv I).measurableEmbedding.eLpNorm_map_measure
    (μ := stdGaussianFin (2 * Fintype.card I)) (g := f) (p := p)
  rw [(coord_preserving I).map_eq] at h
  exact h.symm

def flattenPolynomial (P : MvPolynomial (Fin 2 × I) ℝ) :
    MvPolynomial (Fin (2 * Fintype.card I)) ℝ := MvPolynomial.rename (coordIndex I).symm P

theorem eval_flatten (P : MvPolynomial (Fin 2 × I) ℝ) (x : Fin (2 * Fintype.card I) → ℝ) :
    MvPolynomial.eval x (flattenPolynomial I P) = MvPolynomial.eval (coordEquiv I x) P := by
  simp only [flattenPolynomial, MvPolynomial.eval_rename]
  have he : x ∘ (coordIndex I).symm = coordEquiv I x := by
    funext c
    exact (coord_apply I x c).symm
  rw [he]


end CertificationGaussian
