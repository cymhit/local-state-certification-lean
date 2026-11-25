import CertificationGaussian.ProjectorSubsetOperator
import CertificationGaussian.HilbertFrameTransform
import CertificationGaussian.KernelOperator

/-! # Genuine arbitrary-outcome product frames and Gaussian variance

The actual product reference law and first matrix moments imply the frame bound.
The signed complement map is the physical operator, and the Gaussian variance
uses the already proved noncommuting covariance integrated over this law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem tensorCoordinateVector_norm_sq (v : S → EuclideanSpace ℂ I) :
    ‖tensorCoordinateVector v‖^2 = ∏ s, ‖v s‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, tensorCoordinateVector]
  simp_rw [norm_prod, ← Finset.prod_pow]
  exact (Fintype.prod_sum (fun s i => ‖v s i‖^2)).symm

omit [DecidableEq I] in
theorem tensorCoordinateVector_unit (v : S → EuclideanSpace ℂ I) (hv : ∀ s, ‖v s‖ = 1) :
    ‖tensorCoordinateVector v‖ = 1 := by
  have h := tensorCoordinateVector_norm_sq v
  simp only [hv, one_pow, Finset.prod_const_one] at h
  nlinarith [norm_nonneg (tensorCoordinateVector v)]

omit [DecidableEq S] [Fintype I] [DecidableEq I] in
theorem vectorRankOne_tensorCoordinateVector (v : S → EuclideanSpace ℂ I) :
    vectorRankOne (tensorCoordinateVector v) (tensorCoordinateVector v) =
      wickTensorMatrix (fun s => vectorRankOne (v s) (v s)) := by
  ext x y
  simp [vectorRankOne, tensorCoordinateVector, wickTensorMatrix, star_prod, Finset.prod_mul_distrib]

omit [DecidableEq S] [Fintype I] [DecidableEq I] in
theorem tensorCoordinateVector_continuous :
    Continuous (tensorCoordinateVector (S := S) (I := I)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro a
  exact continuous_finsetProd _ fun s _ =>
    (PiLp.continuous_apply 2 _ (a s)).comp (continuous_apply s)

section Product
variable {Ω : S → Type*} [∀ s, MeasurableSpace (Ω s)]
  (ν : (s : S) → Measure (Ω s)) [∀ s, IsProbabilityMeasure (ν s)]
  (u : (s : S) → Ω s → EuclideanSpace ℂ I) (hm : ∀ s, Measurable (u s))
  (hu : ∀ s t, ‖u s t‖ = 1)

include hm in
omit [DecidableEq S] [DecidableEq I] in
theorem productUnitVector_measurable :
    Measurable (fun ω : (s : S) → Ω s => tensorCoordinateVector (fun s => u s (ω s))) :=
  tensorCoordinateVector_continuous.measurable.comp (measurable_pi_iff.mpr fun s =>
    (hm s).comp (measurable_pi_apply s))

include hm hu

theorem productUnitVector_projector_mean
    (hmean : ∀ s, (∫ t, vectorRankOne (u s t) (u s t) ∂ν s) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) :
    (∫ ω : (s : S) → Ω s, vectorRankOne (tensorCoordinateVector (fun s => u s (ω s)))
      (tensorCoordinateVector (fun s => u s (ω s))) ∂Measure.pi ν) =
        (Fintype.card (S → I) : ℂ)⁻¹ • (1 : Matrix (S → I) (S → I) ℂ) := by
  have hi (s : S) := measurableRankOne_integrable (ν s) (u s) (hm s).aestronglyMeasurable
    (Filter.Eventually.of_forall (hu s))
  simp_rw [vectorRankOne_tensorCoordinateVector]
  rw [integral_wickTensorMatrix ν _ hi]
  simp only [hmean]
  rw [wickTensorMatrix_scalar_one]
  simp

theorem productRankOneFrame_norm_le
    (hmean : ∀ s, (∫ t, vectorRankOne (u s t) (u s t) ∂ν s) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ)) :
    ‖integralHilbertFrame (Measure.pi ν) (fun ω : (s : S) → Ω s => matrixHilbertSchmidt
      (vectorRankOne (tensorCoordinateVector (fun s => u s (ω s)))
        (tensorCoordinateVector (fun s => u s (ω s)))))‖ ≤ (Fintype.card (S → I) : ℝ)⁻¹ := by
  apply measurableRankOneFrame_norm_le (Measure.pi ν) _
    (productUnitVector_measurable u hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => tensorCoordinateVector_unit _ (fun s => hu s (ω s)))
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  simpa using productUnitVector_projector_mean ν u hm hu hmean

theorem productRankOne_signedFrame_norm_le (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, vectorRankOne (u s t) (u s t) ∂ν s) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (J : Finset ℕ) (θ : ℕ → ℝ) :
    ‖integralMatrixFrame (Measure.pi ν) (fun ω : (s : S) → Ω s =>
      cardinalityProjectorKernel (fun s => vectorRankOne (u s (ω s)) (u s (ω s))) J θ)‖ ≤
      (∑ k ∈ J, |θ k|)^2 / (Fintype.card (S → I) : ℝ) := by
  let V := fun ω : (s : S) → Ω s => matrixHilbertSchmidt
    (vectorRankOne (tensorCoordinateVector (fun s => u s (ω s)))
      (tensorCoordinateVector (fun s => u s (ω s))))
  let R := cardinalityComplementRealOperator (S := S) (I := I) J θ
  have hcont : Continuous (fun v : EuclideanSpace ℂ (S → I) => matrixHilbertSchmidt (vectorRankOne v v)) := by
    unfold matrixHilbertSchmidt vectorRankOne
    fun_prop
  have hmV : AEStronglyMeasurable V (Measure.pi ν) :=
    (hcont.measurable.comp (productUnitVector_measurable u hm)).aestronglyMeasurable
  have hbV : ∀ᵐ ω ∂Measure.pi ν, ‖V ω‖ ≤ 1 := Filter.Eventually.of_forall fun ω => by
    have hn := tensorCoordinateVector_unit (fun s => u s (ω s)) (fun s => hu s (ω s))
    have hs : ‖V ω‖^2 = 1 := by
      dsimp only [V]
      rw [matrixHilbertSchmidt_norm_sq _ (vectorRankOne_self_hermitian _),
        vectorRankOne_self_sq _ hn, vectorRankOne_self_trace _ hn, Complex.one_re]
    nlinarith [norm_nonneg (V ω)]
  have he (ω : (s : S) → Ω s) : R (V ω) = matrixHilbertSchmidt
      (cardinalityProjectorKernel (fun s => vectorRankOne (u s (ω s)) (u s (ω s))) J θ) := by
    dsimp only [R, V]
    rw [vectorRankOne_tensorCoordinateVector]
    exact cardinalityComplementRealOperator_matrix hd J θ _ (fun s => vectorRankOne_self_trace _ (hu s (ω s)))
  have hmap := integralHilbertFrame_map_norm (Measure.pi ν) V hmV (by norm_num : (0 : ℝ) ≤ 1) hbV R
  have hL : 0 ≤ ∑ k ∈ J, |θ k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hR : ‖R‖^2 ≤ (∑ k ∈ J, |θ k|)^2 :=
    (sq_le_sq₀ (norm_nonneg R) hL).mpr (cardinalityComplementRealOperator_norm_le hd J θ)
  calc
    _ ≤ ‖R‖^2 * ‖integralHilbertFrame (Measure.pi ν) V‖ := by
      simpa only [he, integralMatrixFrame] using hmap
    _ ≤ (∑ k ∈ J, |θ k|)^2 * (Fintype.card (S → I) : ℝ)⁻¹ :=
      mul_le_mul hR (productRankOneFrame_norm_le ν u hm hu hmean) (norm_nonneg _) (sq_nonneg _)
    _ = _ := by rw [div_eq_mul_inv]

theorem productRankOne_signed_frame_variance (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, vectorRankOne (u s t) (u s t) ∂ν s) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    let B := fun ω : (s : S) → Ω s =>
      cardinalityProjectorKernel (fun s => vectorRankOne (u s (ω s)) (u s (ω s))) J θ
    ‖integralMatrixFrame (Measure.pi ν) B‖ ≤ (∑ k ∈ J, |θ k|)^2 / (Fintype.card I : ℝ)^(Fintype.card S) ∧
    variance (measurableQuadraticEnsemble (Measure.pi ν) B) (pairedGaussian (S → I)) ≤
      8 * (∑ k ∈ J, |θ k|)^2 * kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ /
        (Fintype.card I : ℝ)^(Fintype.card S) := by
  let P := fun s t => vectorRankOne (u s t) (u s t)
  let B := fun ω : (s : S) → Ω s => cardinalityProjectorKernel (fun s => P s (ω s)) J θ
  let v := kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ
  let L := ∑ k ∈ J, |θ k|
  have hi (s : S) : Integrable (P s) (ν s) := measurableRankOne_integrable (ν s) (u s)
    (hm s).aestronglyMeasurable (Filter.Eventually.of_forall (hu s))
  have hh (s : S) (t : Ω s) : (P s t).IsHermitian := vectorRankOne_self_hermitian _
  have hp (s : S) (t : Ω s) : P s t * P s t = P s t := by
    simpa only [pow_two] using vectorRankOne_self_sq (u s t) (hu s t)
  have ht (s : S) (t : Ω s) : (P s t).trace = 1 := vectorRankOne_self_trace _ (hu s t)
  have hmB : AEStronglyMeasurable B (Measure.pi ν) :=
    (cardinalityProjectorKernel_integrable ν P hi J θ).aestronglyMeasurable
  have hhB : ∀ᵐ ω ∂Measure.pi ν, (B ω).IsHermitian := Filter.Eventually.of_forall fun ω =>
    cardinalityProjectorKernel_hermitian _ (fun s => hh s (ω s)) J θ
  have hv : 0 ≤ v := kernelVarianceScale_nonneg _ _ _ _
  have hL : 0 ≤ L := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hvL : v ≤ L^2 := by
    simpa only [v, L, kernelWeightL1] using kernelVarianceScale_le_weight_sq hd J hJ θ
  have hb : ∀ᵐ ω ∂Measure.pi ν, ‖matrixHilbertSchmidt (B ω)‖ ≤ L :=
    Filter.Eventually.of_forall fun ω => by
      have hs := cardinalityProjectorKernel_hilbertSchmidt_sq _ (fun s => hh s (ω s))
        (fun s => hp s (ω s)) (fun s => ht s (ω s)) hd J θ hJ
      change ‖matrixHilbertSchmidt (B ω)‖^2 = v at hs
      nlinarith [norm_nonneg (matrixHilbertSchmidt (B ω))]
  have htrace : (∫ ω, ((B ω)^2).trace.re ∂Measure.pi ν) = v := by
    have he (ω : (s : S) → Ω s) : ((B ω)^2).trace.re = v := by
      simpa only [Complex.ofReal_re] using congrArg Complex.re
        (cardinalityProjectorKernel_trace_square (fun s => P s (ω s))
          (fun s => hp s (ω s)) (fun s => ht s (ω s)) hd J θ hJ)
    simp_rw [he]
    simp
  have hsecond : integralMatrixSecondMoment (Measure.pi ν) B =
      (((v / (Fintype.card (S → I) : ℝ)) : ℝ) : ℂ) • (1 : Matrix (S → I) (S → I) ℂ) := by
    simpa only [integralMatrixSecondMoment, B, v, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_pow, Fintype.card_fun, Nat.cast_pow] using
        cardinalityProjectorKernel_integral_square ν P hi hp hd hmean J θ hJ
  have hf : ‖integralMatrixFrame (Measure.pi ν) B‖ ≤ L^2 / (Fintype.card (S → I) : ℝ) :=
    productRankOne_signedFrame_norm_le ν u hm hu hd hmean J θ
  constructor
  · simpa only [B, P, L, Fintype.card_fun, Nat.cast_pow] using hf
  · have h := measurableQuadraticEnsemble_variance_le_eight (Measure.pi ν) B hmB hhB hL hb
      v L hv hvL htrace hsecond hf
    simpa only [B, P, L, v, Fintype.card_fun, Nat.cast_pow] using h

end Product
end CertificationGaussian
