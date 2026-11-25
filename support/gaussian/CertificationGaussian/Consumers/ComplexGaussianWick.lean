import CertificationGaussian.ComplexGaussianWick

noncomputable section
open MeasureTheory MvPolynomial
open scoped BigOperators
namespace CertificationGaussian.Consumers

/-- Arbitrary finite-dimensional, arbitrary-order repeated-coordinate moment of the actual CN(0,1) variable. -/
theorem repeated_coordinate_factorial {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (i : I) :
    (∫ x, star (complexCoordinate x i)^n * complexCoordinate x i^n ∂pairedGaussian I) =
      (n.factorial : ℂ) := complexGaussian_same_coordinate_moment n i

/-- Sixteen total polynomial degrees count 8!, including every repeated-label pairing. -/
theorem repeated_coordinate_eighth {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    (∫ x, star (complexCoordinate x i)^8 * complexCoordinate x i^8 ∂pairedGaussian I) =
      (40320 : ℂ) := by
  norm_num [Nat.factorial] at ⊢
  simpa [Nat.factorial] using repeated_coordinate_factorial 8 i

/-- The zero-order identity is valid even with no Gaussian coordinates. -/
theorem empty_coordinates_zero_order :
    (∫ x : Fin 2 × Fin 0 → ℝ,
      (∏ a : Fin 0, star (complexCoordinate x (Fin.elim0 a))) *
      (∏ b : Fin 0, complexCoordinate x (Fin.elim0 b)) ∂pairedGaussian (Fin 0)) = (1 : ℂ) := by
  simp [pairedGaussian]

/-- The actual fourth moment exposes both pairings; labels need not be distinct. -/
theorem fourth_moment_two_pairings {I : Type*} [Fintype I] [DecidableEq I]
    (i j : Fin 2 → I) :
    (∫ x, (star (complexCoordinate x (i 0))*star (complexCoordinate x (i 1))) *
      (complexCoordinate x (j 0)*complexCoordinate x (j 1)) ∂pairedGaussian I) =
      (if i 0=j 0 then (1:ℂ) else 0)*(if i 1=j 1 then 1 else 0) +
      (if i 0=j 1 then (1:ℂ) else 0)*(if i 1=j 0 then 1 else 0) :=
  complexGaussian_fourth_moment i j

/-- Products with repeated labels are genuinely integrable, not only formal total integrals. -/
theorem balanced_monomial_integrable {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (i j : Fin n → I) :
    Integrable (fun x => (∏ a, star (complexCoordinate x (i a))) *
      (∏ b, complexCoordinate x (j b))) (pairedGaussian I) := by
  convert complexCoordinatePolyEval_integrable (gaussianBalancedMonomial n i j) using 1
  ext x
  simp only [gaussianBalancedMonomial, gaussianMixedMonomial, complexCoordinatePolyEval,
    map_mul, map_prod,
    show ∀ k, eval (fun c => (x c:ℂ)) (gaussianZPolynomial k) = complexCoordinate x k from
      fun k => complexCoordinatePolyEval_z k x,
    show ∀ k, eval (fun c => (x c:ℂ)) (gaussianBarZPolynomial k) = star (complexCoordinate x k) from
      fun k => complexCoordinatePolyEval_barz k x]

/-- Coincident labels yield two, whereas two distinct coordinates yield one. -/
theorem repeated_and_distinct_fourth (i j : Fin 2) (hij : i ≠ j) :
    (∫ x, star (complexCoordinate x i)^2 * complexCoordinate x i^2 ∂pairedGaussian (Fin 2)) = (2:ℂ) ∧
    (∫ x, (star (complexCoordinate x i)*star (complexCoordinate x j)) *
      (complexCoordinate x i*complexCoordinate x j) ∂pairedGaussian (Fin 2)) = (1:ℂ) := by
  constructor
  · simpa using repeated_coordinate_factorial 2 i
  · simpa [hij, Ne.symm hij] using complexGaussian_fourth_moment ![i,j] ![i,j]

end CertificationGaussian.Consumers
