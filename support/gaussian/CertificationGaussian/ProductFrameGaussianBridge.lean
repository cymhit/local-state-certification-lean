import CertificationGaussian.PhysicalProductFrame
import CertificationGaussian.MeasurableFrameRadial

/-! # Actual product ensembles behind the complex tensor frame

The real restriction of the complex tensor frame agrees with the actual real
ensemble frame on Hermitian inputs. This is the exact domain needed for the
Gaussian observable, identity action and sphere score. No equality on arbitrary
complex matrices is asserted. All moments and bounds below use the original
product reference measure and literal signed cardinality kernel.
-/

noncomputable section
open MeasureTheory Matrix Metric
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]
  {Ω : S → Type*} [∀ s, MeasurableSpace (Ω s)]

def productFrameKernel (u : (s : S) → Ω s → EuclideanSpace ℂ I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (ω : (s : S) → Ω s) : Matrix (S → I) (S → I) ℂ :=
  cardinalityProjectorKernel (fun s => vectorRankOne (u s (ω s)) (u s (ω s))) J θ

omit [∀ s, MeasurableSpace (Ω s)] in
theorem productFrameKernel_hermitian (u : (s : S) → Ω s → EuclideanSpace ℂ I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (ω : (s : S) → Ω s) :
    (productFrameKernel u J θ ω).IsHermitian :=
  cardinalityProjectorKernel_hermitian _ (fun _ => vectorRankOne_self_hermitian _) J θ

omit [∀ s, MeasurableSpace (Ω s)] in
theorem productFrameKernel_norm_le (u : (s : S) → Ω s → EuclideanSpace ℂ I)
    (hu : ∀ s t, ‖u s t‖ = 1) (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (ω : (s : S) → Ω s) :
    ‖matrixHilbertSchmidt (productFrameKernel u J θ ω)‖ ≤ kernelWeightL1 J θ := by
  have hsq := cardinalityProjectorKernel_hilbertSchmidt_sq
    (fun s => vectorRankOne (u s (ω s)) (u s (ω s)))
    (fun _ => vectorRankOne_self_hermitian _)
    (fun s => by simpa only [pow_two] using vectorRankOne_self_sq (u s (ω s)) (hu s (ω s)))
    (fun s => vectorRankOne_self_trace (u s (ω s)) (hu s (ω s))) hd J θ hJ
  change ‖matrixHilbertSchmidt (productFrameKernel u J θ ω)‖^2 = _ at hsq
  have hv := kernelVarianceScale_le_weight_sq hd J hJ θ
  have hL := kernelWeightL1_nonneg J θ
  nlinarith [norm_nonneg (matrixHilbertSchmidt (productFrameKernel u J θ ω))]

omit [∀ s, MeasurableSpace (Ω s)] in
theorem productFrameKernel_trace (u : (s : S) → Ω s → EuclideanSpace ℂ I)
    (hu : ∀ s t, ‖u s t‖ = 1) (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (hθ : ∑ k ∈ J, θ k = 1) (ω : (s : S) → Ω s) :
    (productFrameKernel u J θ ω).trace = 1 := by
  change (cardinalityProjectorKernel _ J θ).trace = _
  rw [cardinalityProjectorKernel_trace _
    (fun s => vectorRankOne_self_trace (u s (ω s)) (hu s (ω s))) hd J θ hJ, hθ, Complex.ofReal_one]

variable (ν : (s : S) → Measure (Ω s)) [∀ s, IsProbabilityMeasure (ν s)]
  (u : (s : S) → Ω s → EuclideanSpace ℂ I) (hm : ∀ s, Measurable (u s))
  (hu : ∀ s t, ‖u s t‖ = 1)

include hm hu in
theorem productFrameKernel_integrable (J : Finset ℕ) (θ : ℕ → ℝ) :
    Integrable (productFrameKernel u J θ) (Measure.pi ν) :=
  cardinalityProjectorKernel_integrable ν _ (fun s => measurableRankOne_integrable
    (ν s) (u s) (hm s).aestronglyMeasurable (ae_of_all _ (hu s))) J θ

include hu in
theorem productFrameKernel_trace_second (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    (∫ ω, ((productFrameKernel u J θ ω)^2).trace.re ∂Measure.pi ν) =
      kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ := by
  have he (ω : (s : S) → Ω s) : ((productFrameKernel u J θ ω)^2).trace.re =
      kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ := by
    simpa only [productFrameKernel, Complex.ofReal_re] using congrArg Complex.re (cardinalityProjectorKernel_trace_square
      (fun s => vectorRankOne (u s (ω s)) (u s (ω s)))
      (fun s => by simpa only [pow_two] using vectorRankOne_self_sq (u s (ω s)) (hu s (ω s)))
      (fun s => vectorRankOne_self_trace _ (hu s (ω s))) hd J θ hJ)
  simp_rw [he]
  simp

include hm hu in
theorem productFrame_real_on_hermitian (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (A : Matrix (S → I) (S → I) ℂ) (hA : A.IsHermitian) :
    (signedProductMatrixFrame J θ (fun s => integralComplexMatrixFrame (ν s)
      (fun t => vectorRankOne (u s t) (u s t)))).restrictScalars ℝ (matrixHilbertSchmidt A) =
      integralMatrixFrame (Measure.pi ν) (productFrameKernel u J θ) (matrixHilbertSchmidt A) := by
  have hc (s : S) : Measurable (fun t => vectorRankOne (u s t) (u s t)) := by
    have h : Continuous (fun v : EuclideanSpace ℂ I => vectorRankOne v v) := by
      unfold vectorRankOne
      fun_prop
    exact h.measurable.comp (hm s)
  have he := integralComplexMatrixFrame_signedProduct ν
    (fun s t => vectorRankOne (u s t) (u s t)) hc
    (fun s t => matrixHilbertSchmidt_unitProjector_norm _ (hu s t))
    (fun s t => vectorRankOne_self_trace _ (hu s t)) hd J θ
  change (signedProductMatrixFrame J θ _).restrictScalars ℝ _ = _
  rw [← he]
  exact integralComplexMatrixFrame_eq_real_on_hermitian (Measure.pi ν) (productFrameKernel u J θ)
    (productFrameKernel_integrable ν u hm hu J θ).aestronglyMeasurable
    (ae_of_all _ (productFrameKernel_hermitian u J θ)) (kernelWeightL1_nonneg J θ)
    (ae_of_all _ (productFrameKernel_norm_le u hu hd J θ hJ)) A hA

include hm hu in
theorem productFrame_gaussian_eq (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (x : Fin 2 × (S → I) → ℝ) :
    inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
      ((signedProductMatrixFrame J θ (fun s => integralComplexMatrixFrame (ν s)
        (fun t => vectorRankOne (u s t) (u s t)))).restrictScalars ℝ
        (matrixHilbertSchmidt (gaussianCenteredProjector x))) =
      measurableQuadraticEnsemble (Measure.pi ν) (productFrameKernel u J θ) x := by
  rw [productFrame_real_on_hermitian ν u hm hu hd J θ hJ _ (gaussianCenteredProjector_hermitian x)]
  exact (measurableQuadraticEnsemble_eq_frame (Measure.pi ν) (productFrameKernel u J θ)
    (productFrameKernel_integrable ν u hm hu J θ).aestronglyMeasurable
    (ae_of_all _ (productFrameKernel_hermitian u J θ)) (kernelWeightL1_nonneg J θ)
    (ae_of_all _ (productFrameKernel_norm_le u hu hd J θ hJ)) x).symm

include hm hu in
theorem productFrameKernel_mean (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, vectorRankOne (u s t) (u s t) ∂ν s) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (hθ : ∑ k ∈ J, θ k = 1) :
    (∫ ω, productFrameKernel u J θ ω ∂Measure.pi ν) =
      (Fintype.card (S → I):ℝ)⁻¹ • (1 : Matrix (S → I) (S → I) ℂ) := by
  have hi := cardinalityProjectorKernel_integral ν (fun s t => vectorRankOne (u s t) (u s t))
    (fun s => measurableRankOne_integrable (ν s) (u s) (hm s).aestronglyMeasurable (ae_of_all _ (hu s)))
    hd hmean J θ hJ
  change (∫ ω, productFrameKernel u J θ ω ∂Measure.pi ν) = _ at hi
  rw [hi, hθ, Complex.ofReal_one, one_div]
  ext i j
  simp only [Matrix.smul_apply, Fintype.card_fun, Nat.cast_pow, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast, smul_eq_mul]

include hm hu in
theorem productFrameKernel_second (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, vectorRankOne (u s t) (u s t) ∂ν s) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    integralMatrixSecondMoment (Measure.pi ν) (productFrameKernel u J θ) =
      ((kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ /
        (Fintype.card (S → I):ℝ) : ℝ) : ℂ) • (1 : Matrix (S → I) (S → I) ℂ) := by
  have h := cardinalityProjectorKernel_integral_square ν (fun s t => vectorRankOne (u s t) (u s t))
    (fun s => measurableRankOne_integrable (ν s) (u s) (hm s).aestronglyMeasurable (ae_of_all _ (hu s)))
    (fun s t => by simpa only [pow_two] using vectorRankOne_self_sq (u s t) (hu s t)) hd hmean J θ hJ
  simpa only [integralMatrixSecondMoment, productFrameKernel, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_pow, Fintype.card_fun, Nat.cast_pow] using h

include hm hu in
theorem productFrame_identity (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, vectorRankOne (u s t) (u s t) ∂ν s) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (hθ : ∑ k ∈ J, θ k = 1) :
    (signedProductMatrixFrame J θ (fun s => integralComplexMatrixFrame (ν s)
      (fun t => vectorRankOne (u s t) (u s t)))).restrictScalars ℝ
      (matrixHilbertSchmidt (1 : Matrix (S → I) (S → I) ℂ)) =
        (Fintype.card (S → I):ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix (S → I) (S → I) ℂ) := by
  rw [productFrame_real_on_hermitian ν u hm hu hd J θ hJ _ Matrix.isHermitian_one]
  exact integralMatrixFrame_identity (Measure.pi ν) (productFrameKernel u J θ)
    (productFrameKernel_integrable ν u hm hu J θ).aestronglyMeasurable
    (kernelWeightL1_nonneg J θ) (ae_of_all _ (productFrameKernel_norm_le u hu hd J θ hJ))
    (ae_of_all _ (productFrameKernel_hermitian u J θ))
    (ae_of_all _ (productFrameKernel_trace u hu hd J θ hJ hθ))
    (productFrameKernel_mean ν u hm hu hd hmean J θ hJ hθ)

include hm hu in
theorem productFrame_sphereScore_eq_integral (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (hθ : ∑ k ∈ J, θ k = 1) (ψ : sphere (0 : EuclideanSpace ℂ (S → I)) 1) :
    gaussianFrameSphereScore ((signedProductMatrixFrame J θ (fun s => integralComplexMatrixFrame (ν s)
      (fun t => vectorRankOne (u s t) (u s t)))).restrictScalars ℝ) ψ =
      ∫ ω, ((Fintype.card (S → I):ℝ)*(sphereQuadraticForm (productFrameKernel u J θ ω) ψ).re-1)^2
        ∂Measure.pi ν := by
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card I)
  let A : Matrix (S → I) (S → I) ℂ := vectorRankOne (ψ : EuclideanSpace ℂ (S → I)) ψ -
    (Fintype.card (S → I):ℝ)⁻¹ • 1
  have hA : A.IsHermitian := (vectorRankOne_self_hermitian _).sub
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint ((Fintype.card (S → I):ℝ)⁻¹) from rfl))
  have he : gaussianFrameSphereScore ((signedProductMatrixFrame J θ (fun s => integralComplexMatrixFrame (ν s)
      (fun t => vectorRankOne (u s t) (u s t)))).restrictScalars ℝ) ψ =
      gaussianFrameSphereScore (integralMatrixFrame (Measure.pi ν) (productFrameKernel u J θ)) ψ := by
    change (Fintype.card (S → I):ℝ)^2 * inner ℝ (matrixHilbertSchmidt A)
      ((signedProductMatrixFrame J θ (fun s => integralComplexMatrixFrame (ν s)
        (fun t => vectorRankOne (u s t) (u s t)))).restrictScalars ℝ (matrixHilbertSchmidt A)) =
      (Fintype.card (S → I):ℝ)^2 * inner ℝ (matrixHilbertSchmidt A)
        (integralMatrixFrame (Measure.pi ν) (productFrameKernel u J θ) (matrixHilbertSchmidt A))
    rw [productFrame_real_on_hermitian ν u hm hu hd J θ hJ A hA]
  exact he.trans (gaussianFrameSphereScore_eq_integral (Measure.pi ν) (productFrameKernel u J θ)
    (productFrameKernel_integrable ν u hm hu J θ).aestronglyMeasurable
    (kernelWeightL1_nonneg J θ) (ae_of_all _ (productFrameKernel_norm_le u hu hd J θ hJ))
    (ae_of_all _ (productFrameKernel_hermitian u J θ))
    (ae_of_all _ (productFrameKernel_trace u hu hd J θ hJ hθ)) ψ)

end CertificationGaussian
