import CertificationGaussian.ComplexMeasurableFrame
import CertificationGaussian.ProductRankOneGaussianFrame

/-! # Tensor products of actual complex frames

Coordinate tensor products act on the full complex Hilbert space. Their norms
and telescoping estimates come from the actual local operators. Product
integration is justified by the measured first moments of vector outer products.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

theorem siteCoordinateLift_sub (s : S)
    (L M : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    siteCoordinateLift s (L-M) = siteCoordinateLift s L-siteCoordinateLift s M := by
  ext x a
  simp only [_root_.sub_apply, PiLp.sub_apply, siteCoordinateLift_apply]

theorem coordinateSubsetLift_norm_le_prod (A : Finset S)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖coordinateSubsetLift A L‖ ≤ ∏ s ∈ A, ‖L s‖ := by
  induction A using Finset.induction_on with
  | empty =>
    rw [coordinateSubsetLift_empty, Finset.prod_empty]
    exact ContinuousLinearMap.norm_id_le
  | @insert s A hs ih =>
    rw [coordinateSubsetLift_insert A s hs, Finset.prod_insert hs]
    exact (norm_mul_le _ _).trans (mul_le_mul (siteCoordinateLift_norm_le s (L s)) ih
      (norm_nonneg _) (norm_nonneg _))

theorem coordinateSubsetLift_norm_le_pow (A : Finset S)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) {c : ℝ}
    (hc : 0 ≤ c) (hL : ∀ s, ‖L s‖ ≤ c) : ‖coordinateSubsetLift A L‖ ≤ c^A.card := by
  induction A using Finset.induction_on with
  | empty =>
    rw [coordinateSubsetLift_empty, Finset.card_empty, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | @insert s A hs ih =>
    rw [coordinateSubsetLift_insert A s hs, Finset.card_insert_of_notMem hs, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul ((siteCoordinateLift_norm_le s (L s)).trans (hL s))
      ih (norm_nonneg _) hc)

theorem coordinateSubsetLift_distance_le (A : Finset S)
    (L M : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hL : ∀ s, ‖L s‖ ≤ c) (hM : ∀ s, ‖M s‖ ≤ c)
    (hd : ∀ s, ‖L s-M s‖ ≤ ε) :
    ‖coordinateSubsetLift A L-coordinateSubsetLift A M‖ ≤
      (A.card : ℝ)*ε*c^(A.card-1) := by
  induction A using Finset.induction_on with
  | empty => simp [coordinateSubsetLift_empty]
  | @insert s A hs ih =>
    rw [coordinateSubsetLift_insert A s hs, coordinateSubsetLift_insert A s hs,
      Finset.card_insert_of_notMem hs, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    have he : siteCoordinateLift s (L s) * coordinateSubsetLift A L -
        siteCoordinateLift s (M s) * coordinateSubsetLift A M =
        siteCoordinateLift s (L s) * (coordinateSubsetLift A L-coordinateSubsetLift A M) +
        (siteCoordinateLift s (L s)-siteCoordinateLift s (M s)) * coordinateSubsetLift A M := by
      rw [mul_sub, sub_mul]
      abel
    rw [he]
    calc
      _ ≤ ‖siteCoordinateLift s (L s) * (coordinateSubsetLift A L-coordinateSubsetLift A M)‖ +
          ‖(siteCoordinateLift s (L s)-siteCoordinateLift s (M s)) * coordinateSubsetLift A M‖ := norm_add_le _ _
      _ ≤ c * ((A.card : ℝ)*ε*c^(A.card-1)) + ε*c^A.card := by
        apply add_le_add
        · exact (norm_mul_le _ _).trans (mul_le_mul
            ((siteCoordinateLift_norm_le s (L s)).trans (hL s)) ih (norm_nonneg _) hc)
        · rw [← siteCoordinateLift_sub]
          exact (norm_mul_le _ _).trans (mul_le_mul
            ((siteCoordinateLift_norm_le s (L s-M s)).trans (hd s))
            (coordinateSubsetLift_norm_le_pow A M hc hM) (norm_nonneg _) hε)
      _ = _ := by
        by_cases hA : A.card = 0
        · simp [hA]
        · have hn : A.card-1+1 = A.card := by omega
          have hp : c*c^(A.card-1) = c^A.card := by rw [← pow_succ', hn]
          calc
            _ = (A.card : ℝ)*ε*(c*c^(A.card-1)) + ε*c^A.card := by ring
            _ = _ := by rw [hp]; ring

/-- The full tensor perturbation bound, including the empty product. -/
theorem coordinateTensorFrame_distance_le
    (L M : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hL : ∀ s, ‖L s‖ ≤ c) (hM : ∀ s, ‖M s‖ ≤ c)
    (hd : ∀ s, ‖L s-M s‖ ≤ ε) :
    ‖coordinateSubsetLift Finset.univ L-coordinateSubsetLift Finset.univ M‖ ≤
      (Fintype.card S : ℝ)*ε*c^(Fintype.card S-1) := by
  simpa only [Finset.card_univ] using coordinateSubsetLift_distance_le Finset.univ L M hc hε hL hM hd

omit [DecidableEq S] [Fintype I] in
theorem tensorCoordinateVector_single (b : S → I) :
    tensorCoordinateVector (fun s => WithLp.toLp 2 (Pi.single (b s) 1 : I → ℂ)) =
      WithLp.toLp 2 (Pi.single b 1 : (S → I) → ℂ) := by
  apply PiLp.ext
  intro a
  change (∏ s, (Pi.single (b s) 1 : I → ℂ) (a s)) = (Pi.single b 1 : (S → I) → ℂ) a
  by_cases hab : a = b
  · subst a; simp
  · rw [Pi.single_eq_of_ne hab]
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hab
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [hs]

theorem toEuclideanCLM_wickTensorMatrix (A : S → Matrix I I ℂ) :
    Matrix.toEuclideanCLM (n := S → I) (𝕜 := ℂ) (wickTensorMatrix A) =
      coordinateSubsetLift Finset.univ (fun s => Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (A s)) := by
  ext x a
  rw [euclideanOperator_expansion, euclideanOperator_expansion]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [← tensorCoordinateVector_single b, coordinateSubsetLift_product]
  change (∑ j, wickTensorMatrix A a j * tensorCoordinateVector
    (fun s => WithLp.toLp 2 (Pi.single (b s) 1)) j) =
      ∏ s, (if s ∈ Finset.univ then Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (A s)
        (WithLp.toLp 2 (Pi.single (b s) 1)) else WithLp.toLp 2 (Pi.single (b s) 1)) (a s)
  rw [tensorCoordinateVector_single]
  simp [wickTensorMatrix, Matrix.mulVec, dotProduct, Pi.single_apply]

private def tensorFrameMatrixCLM : Matrix I I ℂ →L[ℂ]
    (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
      map_add' := by intro A B; exact map_add _ A B
      map_smul' := by intro c A; exact map_smul _ c A }

theorem toEuclideanCLM_vectorRankOne (v w : EuclideanSpace ℂ I) :
    Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (vectorRankOne v w) = InnerProductSpace.rankOne ℂ v w := by
  ext x i
  change (∑ j, (v i * star (w j)) * x j) = (inner ℂ w x) * v i
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.star_apply]
  ring

omit [Fintype S] [DecidableEq S] in
theorem integralComplexHilbertFrame_eq_matrix_integral
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → EuclideanSpace ℂ I)
    (hi : Integrable (fun s => vectorRankOne (V s) (V s)) ν) :
    integralComplexHilbertFrame ν V =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (∫ s, vectorRankOne (V s) (V s) ∂ν) := by
  have h := (tensorFrameMatrixCLM (I := I)).integral_comp_comm hi
  change (∫ s, Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (vectorRankOne (V s) (V s)) ∂ν) =
    Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (∫ s, vectorRankOne (V s) (V s) ∂ν) at h
  simpa only [toEuclideanCLM_vectorRankOne, integralComplexHilbertFrame] using h

/-- Exact Fubini factorization of the actual complex frame; outcomes are arbitrary. -/
theorem integralComplexHilbertFrame_tensor
    {Ω : S → Type*} [∀ s, MeasurableSpace (Ω s)]
    (ν : (s : S) → Measure (Ω s)) [∀ s, IsProbabilityMeasure (ν s)]
    (V : (s : S) → Ω s → EuclideanSpace ℂ I)
    (hm : ∀ s, Measurable (V s)) (hu : ∀ s t, ‖V s t‖ = 1) :
    integralComplexHilbertFrame (Measure.pi ν)
      (fun ω : (s : S) → Ω s => tensorCoordinateVector (fun s => V s (ω s))) =
      coordinateSubsetLift Finset.univ (fun s => integralComplexHilbertFrame (ν s) (V s)) := by
  have hi (s : S) := measurableRankOne_integrable (ν s) (V s) (hm s).aestronglyMeasurable
    (ae_of_all _ (hu s))
  have hglobal : Integrable (fun ω : (s : S) → Ω s =>
      vectorRankOne (tensorCoordinateVector (fun s => V s (ω s)))
        (tensorCoordinateVector (fun s => V s (ω s)))) (Measure.pi ν) := by
    simpa only [vectorRankOne_tensorCoordinateVector] using
      wickTensorMatrix_integrable ν (fun s t => vectorRankOne (V s t) (V s t)) hi
  rw [integralComplexHilbertFrame_eq_matrix_integral _ _ hglobal]
  simp only [vectorRankOne_tensorCoordinateVector]
  rw [integral_wickTensorMatrix ν _ hi, toEuclideanCLM_wickTensorMatrix]
  congr 1
  funext s
  exact (integralComplexHilbertFrame_eq_matrix_integral (ν s) (V s) (hi s)).symm

end CertificationGaussian
