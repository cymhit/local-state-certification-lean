import CertificationGaussian.MeasurableGaussianFrameBound
import CertificationGaussian.GaussianTail

/-! # The actual quartic polynomial of a measurable matrix frame

The polynomial is formed from the real coordinates of the genuine matrix
`zz† - I` and an arbitrary real continuous linear operator on Hilbert--Schmidt
space. Its evaluation and degree are proved before hypercontractivity is used.
The measurable-ensemble specialization therefore imposes no finite-outcome
or orthogonality restriction on the reference probability.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators ENNReal
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

private def scaledCoordinatePolynomial (k : Fin 2) (i : I) : MvPolynomial (Fin 2 × I) ℝ :=
  C ((Real.sqrt 2)⁻¹) * X (k,i)

private def centeredProjectorRealPolynomial (i j : I) : MvPolynomial (Fin 2 × I) ℝ :=
  scaledCoordinatePolynomial 0 i * scaledCoordinatePolynomial 0 j +
    scaledCoordinatePolynomial 1 i * scaledCoordinatePolynomial 1 j - C (if i=j then 1 else 0)

private def centeredProjectorImagPolynomial (i j : I) : MvPolynomial (Fin 2 × I) ℝ :=
  scaledCoordinatePolynomial 1 i * scaledCoordinatePolynomial 0 j -
    scaledCoordinatePolynomial 0 i * scaledCoordinatePolynomial 1 j

omit [Fintype I] in
private theorem centeredProjectorRealPolynomial_eval (i j : I) (x : Fin 2 × I → ℝ) :
    eval x (centeredProjectorRealPolynomial i j) = (gaussianCenteredProjector x i j).re := by
  have hs : (Real.sqrt 2)⁻¹ = (2:ℝ)⁻¹ * Real.sqrt 2 := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  by_cases hij : i=j <;> simp [centeredProjectorRealPolynomial, scaledCoordinatePolynomial, gaussianCenteredProjector,
    vectorRankOne, complexCoordinate, Complex.mul_re, div_eq_mul_inv,
    mul_comm, hs, hij]

omit [Fintype I] in
private theorem centeredProjectorImagPolynomial_eval (i j : I) (x : Fin 2 × I → ℝ) :
    eval x (centeredProjectorImagPolynomial i j) = (gaussianCenteredProjector x i j).im := by
  have hs : (Real.sqrt 2)⁻¹ = (2:ℝ)⁻¹ * Real.sqrt 2 := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  simp [centeredProjectorImagPolynomial, scaledCoordinatePolynomial, gaussianCenteredProjector,
    vectorRankOne, complexCoordinate, Matrix.one_apply, Complex.mul_im, div_eq_mul_inv,
    mul_comm, hs, apply_ite]
  ring

omit [Fintype I] [DecidableEq I] in
private theorem scaledCoordinatePolynomial_degree (k : Fin 2) (i : I) :
    (scaledCoordinatePolynomial k i).totalDegree ≤ 1 :=
  (degree_C_mul _ _).trans (by simp)

omit [Fintype I] in
private theorem centeredProjectorRealPolynomial_degree (i j : I) :
    (centeredProjectorRealPolynomial i j).totalDegree ≤ 2 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply (totalDegree_add _ _).trans
  apply max_le <;> apply (totalDegree_mul _ _).trans
  · exact Nat.add_le_add (scaledCoordinatePolynomial_degree _ _) (scaledCoordinatePolynomial_degree _ _)
  · exact Nat.add_le_add (scaledCoordinatePolynomial_degree _ _) (scaledCoordinatePolynomial_degree _ _)

omit [Fintype I] [DecidableEq I] in
private theorem centeredProjectorImagPolynomial_degree (i j : I) :
    (centeredProjectorImagPolynomial i j).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  apply max_le <;> apply (totalDegree_mul _ _).trans
  · exact Nat.add_le_add (scaledCoordinatePolynomial_degree _ _) (scaledCoordinatePolynomial_degree _ _)
  · exact Nat.add_le_add (scaledCoordinatePolynomial_degree _ _) (scaledCoordinatePolynomial_degree _ _)

private def hsCoordinateVector (c : Fin 2 × (I × I)) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (Pi.single c.2 (if c.1=0 then 1 else Complex.I))

private def hsCoordinate (c : Fin 2 × (I × I)) (z : EuclideanSpace ℂ (I × I)) : ℝ :=
  if c.1=0 then (z c.2).re else (z c.2).im

private theorem hsCoordinate_expansion (z : EuclideanSpace ℂ (I × I)) :
    (∑ c, hsCoordinate c z • hsCoordinateVector c) = z := by
  ext ij
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, hsCoordinate, hsCoordinateVector,
    Pi.single_apply, Prod.ext_iff, ite_and, Complex.re_add_im]

private def centeredProjectorCoordinatePolynomial (c : Fin 2 × (I × I)) :
    MvPolynomial (Fin 2 × I) ℝ :=
  if c.1=0 then centeredProjectorRealPolynomial c.2.1 c.2.2
  else centeredProjectorImagPolynomial c.2.1 c.2.2

omit [Fintype I] in
private theorem centeredProjectorCoordinatePolynomial_eval (c : Fin 2 × (I × I))
    (x : Fin 2 × I → ℝ) :
    eval x (centeredProjectorCoordinatePolynomial c) =
      hsCoordinate c (matrixHilbertSchmidt (gaussianCenteredProjector x)) := by
  unfold centeredProjectorCoordinatePolynomial hsCoordinate
  split_ifs
  · exact centeredProjectorRealPolynomial_eval _ _ x
  · exact centeredProjectorImagPolynomial_eval _ _ x

omit [Fintype I] in
private theorem centeredProjectorCoordinatePolynomial_degree (c : Fin 2 × (I × I)) :
    (centeredProjectorCoordinatePolynomial c).totalDegree ≤ 2 := by
  unfold centeredProjectorCoordinatePolynomial
  split_ifs
  · exact centeredProjectorRealPolynomial_degree _ _
  · exact centeredProjectorImagPolynomial_degree _ _

/-- The centered quartic polynomial associated with an actual real HS operator. -/
def gaussianFramePolynomial
    (T : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)) (v : ℝ) :
    MvPolynomial (Fin 2 × I) ℝ :=
  (∑ c : Fin 2 × (I × I), ∑ e : Fin 2 × (I × I),
    C (inner ℝ (hsCoordinateVector c) (T (hsCoordinateVector e))) *
      centeredProjectorCoordinatePolynomial c * centeredProjectorCoordinatePolynomial e) - C v

theorem gaussianFramePolynomial_eval
    (T : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)) (v : ℝ)
    (x : Fin 2 × I → ℝ) :
    eval x (gaussianFramePolynomial T v) =
      inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
        (T (matrixHilbertSchmidt (gaussianCenteredProjector x))) - v := by
  let G := matrixHilbertSchmidt (gaussianCenteredProjector x)
  have hG := hsCoordinate_expansion G
  change _ = inner ℝ G (T G) - v
  conv_rhs => rw [← hG]
  simp only [gaussianFramePolynomial, map_sub, map_sum, map_mul, eval_C,
    centeredProjectorCoordinatePolynomial_eval, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [G]
  ring

theorem gaussianFramePolynomial_degree
    (T : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)) (v : ℝ) :
    (gaussianFramePolynomial T v).totalDegree ≤ 4 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply totalDegree_finsetSum_le
  intro c hc
  apply totalDegree_finsetSum_le
  intro e he
  apply (totalDegree_mul _ _).trans
  exact Nat.add_le_add ((degree_C_mul _ _).trans (centeredProjectorCoordinatePolynomial_degree c))
    (centeredProjectorCoordinatePolynomial_degree e)

section Ensemble
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
  (B : Ω → Matrix I I ℂ) (hB : AEStronglyMeasurable B ν)
  (hH : ∀ᵐ s ∂ν, (B s).IsHermitian) {K : ℝ} (hK : 0 ≤ K)
  (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
include hB hH hK hbound

/-- Exact evaluation of the actual Bochner frame, for arbitrary measurable outcomes. -/
theorem measurableQuadraticEnsemble_centered_eq_polynomial (v : ℝ) (x : Fin 2 × I → ℝ) :
    measurableQuadraticEnsemble ν B x - v =
      eval x (gaussianFramePolynomial (integralMatrixFrame ν B) v) := by
  rw [gaussianFramePolynomial_eval, measurableQuadraticEnsemble_eq_frame ν B hB hH hK hbound]
  rfl

theorem measurableQuadraticEnsemble_centered_eLpNorm (v p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun x => measurableQuadraticEnsemble ν B x - v) (ENNReal.ofReal p) (pairedGaussian I) ≤
      ENNReal.ofReal (5*(p-1)^2) *
        eLpNorm (fun x => measurableQuadraticEnsemble ν B x - v) 2 (pairedGaussian I) := by
  have he : (fun x => measurableQuadraticEnsemble ν B x - v) =
      fun x => eval x (gaussianFramePolynomial (integralMatrixFrame ν B) v) :=
    funext (measurableQuadraticEnsemble_centered_eq_polynomial ν B hB hH hK hbound v)
  rw [he]
  exact paired_quartic_eLpNorm I _ (gaussianFramePolynomial_degree _ v) p hp

theorem measurableQuadraticEnsemble_centered_memLp (v p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun x => measurableQuadraticEnsemble ν B x - v) (ENNReal.ofReal p) (pairedGaussian I) := by
  have he : (fun x => measurableQuadraticEnsemble ν B x - v) =
      fun x => eval x (gaussianFramePolynomial (integralMatrixFrame ν B) v) :=
    funext (measurableQuadraticEnsemble_centered_eq_polynomial ν B hB hH hK hbound v)
  rw [he]
  exact paired_quartic_memLp I _ (gaussianFramePolynomial_degree _ v) p hp

end Ensemble
end CertificationGaussian
