import CertificationGaussian.ProductFrameNet
import CertificationGaussian.ProductFrameGaussianBridge
import CertificationGaussian.MeasurableFrameAsymptotics

/-! # Actual probability witnesses for canonical product frames

Each local frame carries an actual probability measure on the unit sphere.
Selecting that measure requires no measurable dependence on the frame parameter:
the outcome map is always the continuous sphere inclusion. The signed kernel,
its moments, and its Gaussian observable below use this same product measure.
The final cutoff precedes every canonical frame tuple.
-/

noncomputable section
open MeasureTheory Filter Metric
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

def canonicalFrameMeasure (T : canonicalRankOneFrames (I := I)) :
    Measure (sphere (0 : EuclideanSpace ℂ I) 1) := Classical.choose T.property

instance canonicalFrameMeasureProbability (T : canonicalRankOneFrames (I := I)) :
    IsProbabilityMeasure (canonicalFrameMeasure T) := (Classical.choose_spec T.property).1

theorem canonicalFrameMeasure_mean (T : canonicalRankOneFrames (I := I)) :
    (∫ ψ, vectorRankOne ψ.val ψ.val ∂canonicalFrameMeasure T) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ) := (Classical.choose_spec T.property).2.1

theorem canonicalFrameMeasure_frame (T : canonicalRankOneFrames (I := I)) :
    integralComplexMatrixFrame (canonicalFrameMeasure T)
      (fun ψ => vectorRankOne ψ.val ψ.val) = T.val := (Classical.choose_spec T.property).2.2.symm

variable {S : Type*} [Fintype S] [DecidableEq S]

def canonicalProductReference (T : S → canonicalRankOneFrames (I := I)) :
    Measure (S → sphere (0 : EuclideanSpace ℂ I) 1) :=
  Measure.pi (fun s => canonicalFrameMeasure (T s))

instance canonicalProductReferenceProbability (T : S → canonicalRankOneFrames (I := I)) :
    IsProbabilityMeasure (canonicalProductReference T) := by
  unfold canonicalProductReference
  infer_instance

def canonicalProductKernel (J : Finset ℕ) (θ : ℕ → ℝ)
    (ω : S → sphere (0 : EuclideanSpace ℂ I) 1) : Matrix (S → I) (S → I) ℂ :=
  productFrameKernel (fun (_ : S) ψ => ψ.val) J θ ω

omit [Fintype S] [DecidableEq S] in
private theorem canonicalProductFrame_localFrames (T : S → canonicalRankOneFrames (I := I)) :
    (fun s => integralComplexMatrixFrame (canonicalFrameMeasure (T s))
      (fun ψ => vectorRankOne ψ.val ψ.val)) = (fun s => (T s).val) :=
  funext (fun s => canonicalFrameMeasure_frame (T s))

theorem canonicalProductKernel_integrable (T : S → canonicalRankOneFrames (I := I))
    (J : Finset ℕ) (θ : ℕ → ℝ) :
    Integrable (canonicalProductKernel (S := S) (I := I) J θ) (canonicalProductReference T) :=
  productFrameKernel_integrable (fun s => canonicalFrameMeasure (T s))
    (fun (_ : S) ψ => ψ.val) (fun _ => continuous_subtype_val.measurable)
    (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) J θ

theorem canonicalProductKernel_hermitian (J : Finset ℕ) (θ : ℕ → ℝ)
    (ω : S → sphere (0 : EuclideanSpace ℂ I) 1) :
    (canonicalProductKernel J θ ω).IsHermitian := productFrameKernel_hermitian _ J θ ω

theorem canonicalProductKernel_norm_le (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (ω : S → sphere (0 : EuclideanSpace ℂ I) 1) :
    ‖matrixHilbertSchmidt (canonicalProductKernel J θ ω)‖ ≤ kernelWeightL1 J θ :=
  productFrameKernel_norm_le _ (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd J θ hJ ω

theorem canonicalProductKernel_trace (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hJ : ∀ k ∈ J, k ≤ Fintype.card S)
    (hθ : ∑ k ∈ J, θ k = 1) (ω : S → sphere (0 : EuclideanSpace ℂ I) 1) :
    (canonicalProductKernel J θ ω).trace = 1 :=
  productFrameKernel_trace _ (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd J θ hJ hθ ω

theorem canonicalProductKernel_mean (T : S → canonicalRankOneFrames (I := I))
    (hd : 2 ≤ Fintype.card I) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hJ : ∀ k ∈ J, k ≤ Fintype.card S) (hθ : ∑ k ∈ J, θ k = 1) :
    (∫ ω, canonicalProductKernel J θ ω ∂canonicalProductReference T) =
      (Fintype.card (S → I) : ℝ)⁻¹ • (1 : Matrix (S → I) (S → I) ℂ) :=
  productFrameKernel_mean (fun s => canonicalFrameMeasure (T s))
    (fun (_ : S) ψ => ψ.val) (fun _ => continuous_subtype_val.measurable)
    (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd
    (fun s => canonicalFrameMeasure_mean (T s)) J θ hJ hθ

theorem canonicalProductKernel_trace_second (T : S → canonicalRankOneFrames (I := I))
    (hd : 2 ≤ Fintype.card I) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    (∫ ω, ((canonicalProductKernel J θ ω)^2).trace.re ∂canonicalProductReference T) =
      kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ :=
  productFrameKernel_trace_second (fun s => canonicalFrameMeasure (T s))
    (fun (_ : S) ψ => ψ.val) (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd J θ hJ

theorem canonicalProductKernel_second (T : S → canonicalRankOneFrames (I := I))
    (hd : 2 ≤ Fintype.card I) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hJ : ∀ k ∈ J, k ≤ Fintype.card S) :
    integralMatrixSecondMoment (canonicalProductReference T) (canonicalProductKernel J θ) =
      ((kernelVarianceScale (Fintype.card I) (Fintype.card S) J θ /
        (Fintype.card (S → I) : ℝ) : ℝ) : ℂ) • (1 : Matrix (S → I) (S → I) ℂ) :=
  productFrameKernel_second (fun s => canonicalFrameMeasure (T s))
    (fun (_ : S) ψ => ψ.val) (fun _ => continuous_subtype_val.measurable)
    (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd
    (fun s => canonicalFrameMeasure_mean (T s)) J θ hJ

theorem canonicalProductKernel_frame_norm_le (T : S → canonicalRankOneFrames (I := I))
    (hd : 2 ≤ Fintype.card I) (J : Finset ℕ) (θ : ℕ → ℝ) :
    ‖integralMatrixFrame (canonicalProductReference T) (canonicalProductKernel J θ)‖ ≤
      (kernelWeightL1 J θ)^2 / (Fintype.card (S → I) : ℝ) :=
  productRankOne_signedFrame_norm_le (fun s => canonicalFrameMeasure (T s))
    (fun (_ : S) ψ => ψ.val) (fun _ => continuous_subtype_val.measurable)
    (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd
    (fun s => canonicalFrameMeasure_mean (T s)) J θ

theorem canonicalProductFrame_symmetric (T : S → canonicalRankOneFrames (I := I))
    (J : Finset ℕ) (θ : ℕ → ℝ) (X Y : EuclideanSpace ℂ ((S → I) × (S → I))) :
    inner ℝ X ((signedProductMatrixFrame J θ (fun s => (T s).val)).restrictScalars ℝ Y) =
      inner ℝ ((signedProductMatrixFrame J θ (fun s => (T s).val)).restrictScalars ℝ X) Y := by
  apply complexMatrixFrame_restrict_symmetric
  rw [signedProductMatrixFrame_adjoint]
  exact congrArg (signedProductMatrixFrame J θ) (funext (fun s => canonicalRankOneFrame_adjoint (T s)))

theorem canonicalProductFrame_identity (T : S → canonicalRankOneFrames (I := I))
    (hd : 2 ≤ Fintype.card I) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hJ : ∀ k ∈ J, k ≤ Fintype.card S) (hθ : ∑ k ∈ J, θ k = 1) :
    (signedProductMatrixFrame J θ (fun s => (T s).val)).restrictScalars ℝ
      (matrixHilbertSchmidt (1 : Matrix (S → I) (S → I) ℂ)) =
      (Fintype.card (S → I) : ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix (S → I) (S → I) ℂ) := by
  rw [← canonicalProductFrame_localFrames T]
  exact productFrame_identity (fun s => canonicalFrameMeasure (T s))
    (fun (_ : S) ψ => ψ.val) (fun _ => continuous_subtype_val.measurable)
    (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd
    (fun s => canonicalFrameMeasure_mean (T s)) J θ hJ hθ

theorem canonicalProductFrame_gaussian_eq (T : S → canonicalRankOneFrames (I := I))
    (hd : 2 ≤ Fintype.card I) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hJ : ∀ k ∈ J, k ≤ Fintype.card S) (x : Fin 2 × (S → I) → ℝ) :
    inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
      ((signedProductMatrixFrame J θ (fun s => (T s).val)).restrictScalars ℝ
        (matrixHilbertSchmidt (gaussianCenteredProjector x))) =
      measurableQuadraticEnsemble (canonicalProductReference T) (canonicalProductKernel J θ) x := by
  rw [← canonicalProductFrame_localFrames T]
  exact productFrame_gaussian_eq (fun s => canonicalFrameMeasure (T s))
    (fun (_ : S) ψ => ψ.val) (fun _ => continuous_subtype_val.measurable)
    (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd J θ hJ x

theorem canonicalProductFrame_sphereScore_eq_integral (T : S → canonicalRankOneFrames (I := I))
    (hd : 2 ≤ Fintype.card I) (J : Finset ℕ) (θ : ℕ → ℝ)
    (hJ : ∀ k ∈ J, k ≤ Fintype.card S) (hθ : ∑ k ∈ J, θ k = 1)
    (ψ : sphere (0 : EuclideanSpace ℂ (S → I)) 1) :
    gaussianFrameSphereScore ((signedProductMatrixFrame J θ (fun s => (T s).val)).restrictScalars ℝ) ψ =
      ∫ ω, ((Fintype.card (S → I) : ℝ) * (sphereQuadraticForm (canonicalProductKernel J θ ω) ψ).re-1)^2
        ∂canonicalProductReference T := by
  rw [← canonicalProductFrame_localFrames T]
  exact productFrame_sphereScore_eq_integral (fun s => canonicalFrameMeasure (T s))
    (fun (_ : S) ψ => ψ.val) (fun _ => continuous_subtype_val.measurable)
    (fun _ ψ => mem_sphere_zero_iff_norm.mp ψ.property) hd J θ hJ hθ ψ

theorem canonicalProductFrame_eventually_cubic {d : ℕ} (hd : 2 ≤ d)
    (J : Finset ℕ) (θ : ℕ → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : ℕ in atTop, ∀ U : Fin n → canonicalRankOneFrames (I := Fin d),
      pairedGaussian (QuditIndex d n)
        {x | kernelVarianceScale d n J θ / n ≤
          |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
            ((signedProductMatrixFrame J θ (fun s => (U s).val)).restrictScalars ℝ
              (matrixHilbertSchmidt (gaussianCenteredProjector x))) - kernelVarianceScale d n J θ|} ≤
        ENNReal.ofReal (Real.exp (-(Real.log d / 4) * (n : ℝ)^3)) := by
  filter_upwards [measurableQuadraticEnsemble_eventually_cubic.{0} hd J θ hθ,
    eventually_ge_atTop (J.sup id)] with n hn hN
  intro U
  have hd' : 2 ≤ Fintype.card (Fin d) := by simpa only [Fintype.card_fin] using hd
  have hJ : ∀ k ∈ J, k ≤ Fintype.card (Fin n) := by
    intro k hk
    have hk' : k ≤ J.sup id := Finset.le_sup (f := id) hk
    rw [Fintype.card_fin]
    exact hk'.trans hN
  have he := hn (Fin n → sphere (0 : EuclideanSpace ℂ (Fin d)) 1) inferInstance
    (canonicalProductReference U) inferInstance (canonicalProductKernel J θ)
    (canonicalProductKernel_integrable U J θ).aestronglyMeasurable
    (ae_of_all _ (canonicalProductKernel_hermitian J θ)) (kernelWeightL1 J θ)
    (kernelWeightL1_nonneg J θ) (ae_of_all _ (canonicalProductKernel_norm_le hd' J θ hJ))
    (by simpa only [Fintype.card_fin] using canonicalProductKernel_trace_second U hd' J θ hJ)
    (by simpa only [Fintype.card_fin, Fintype.card_fun, Nat.cast_pow] using
      canonicalProductKernel_second U hd' J θ hJ)
    (by simpa only [Fintype.card_fin, Fintype.card_fun, Nat.cast_pow] using
      canonicalProductKernel_frame_norm_le U hd' J θ)
  have hset : {x | kernelVarianceScale d n J θ / n ≤
      |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
        ((signedProductMatrixFrame J θ (fun s => (U s).val)).restrictScalars ℝ
          (matrixHilbertSchmidt (gaussianCenteredProjector x))) - kernelVarianceScale d n J θ|} =
      {x | kernelVarianceScale d n J θ / n ≤
        |measurableQuadraticEnsemble (canonicalProductReference U) (canonicalProductKernel J θ) x -
          kernelVarianceScale d n J θ|} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [canonicalProductFrame_gaussian_eq U hd' J θ hJ x]
  rw [hset]
  exact he

end CertificationGaussian
