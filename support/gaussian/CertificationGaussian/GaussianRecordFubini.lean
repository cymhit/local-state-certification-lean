import CertificationGaussian.FiniteComplementContraction

noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- Explicit finite entry expansion of the four actual normal-ordered blocks on the original Gaussian coordinates. -/
theorem complexGaussian_four_matrix_blocks_positions_eval {I : Type*} [Fintype I] [DecidableEq I]
    (A : Fin 4 × Fin 2 → Matrix I I ℂ) (x : Fin 2 × I → ℝ) :
    (∏ b : Fin 4,complexGaussianNormalMatrix (A (b,0)) (A (b,1)) (complexCoordinate x)) =
      ∑ i : Fin 4 × Fin 2 → I,∑ j : Fin 4 × Fin 2 → I,
        (∏ t,A t (i t) (j t))*complexCoordinatePolyEval
          (∏ b : Fin 4,gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1))) x := by
  have h := congrArg (MvPolynomial.eval (fun t => (x t:ℂ)))
    (gaussianNormalMatrixPolynomial_prod_positions A)
  have he (M N : Matrix I I ℂ) :
      MvPolynomial.eval (fun t => (x t:ℂ)) (gaussianNormalMatrixPolynomial M N)=
        complexGaussianNormalMatrix M N (complexCoordinate x) := gaussianNormalMatrixPolynomial_eval M N x
  simpa only [complexCoordinatePolyEval,map_prod,map_sum,map_mul,eval_C,he] using h

section CompactRecord
variable {Ω I : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
local instance : IsProbabilityMeasure (pairedGaussian I) := by
  unfold pairedGaussian
  infer_instance

/-- Real joint absolute integrability: compact continuous record coefficients times actual Gaussian polynomials.
In particular no interchange of an undefined integral or extra Gaussian moment assumption is used. -/
theorem recordGaussian_four_blocks_integrable
    (A : (Fin 4 × Fin 2) → Ω → Matrix I I ℂ) (hA : ∀ t,Continuous (A t))
    (f : Ω → ℂ) (hf : Continuous f) :
    Integrable (fun y : Ω × (Fin 2 × I → ℝ) => f y.1*
      ∏ b : Fin 4,complexGaussianNormalMatrix (A (b,0) y.1) (A (b,1) y.1) (complexCoordinate y.2))
      (μ.prod (pairedGaussian I)) := by
  have he (y : Ω × (Fin 2 × I → ℝ)) :=
    complexGaussian_four_matrix_blocks_positions_eval (fun t => A t y.1) y.2
  simp_rw [he,Finset.mul_sum,← mul_assoc]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hc : Continuous (fun ω => f ω*∏ t,A t ω (i t) (j t)) := by fun_prop
  have hi : Integrable (fun ω => f ω*∏ t,A t ω (i t) (j t)) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.mul_prod (complexCoordinatePolyEval_integrable
    (∏ b : Fin 4,gaussianNormalQuartic (i (b,0)) (i (b,1)) (j (b,0)) (j (b,1))))

/-- Actual Gaussian and compact-record integrals can therefore be swapped for all four normal-ordered blocks. -/
theorem recordGaussian_four_blocks_swap
    (A : (Fin 4 × Fin 2) → Ω → Matrix I I ℂ) (hA : ∀ t,Continuous (A t))
    (f : Ω → ℂ) (hf : Continuous f) :
    (∫ ω,∫ x,f ω*∏ b : Fin 4,complexGaussianNormalMatrix (A (b,0) ω) (A (b,1) ω)
      (complexCoordinate x) ∂pairedGaussian I ∂μ) =
    ∫ x,∫ ω,f ω*∏ b : Fin 4,complexGaussianNormalMatrix (A (b,0) ω) (A (b,1) ω)
      (complexCoordinate x) ∂μ ∂pairedGaussian I :=
  integral_integral_swap (recordGaussian_four_blocks_integrable μ A hA f hf)

end CompactRecord

/-- Four independent complete records recover the fourth power of the actual averaged matrix. -/
theorem fourReadout_matrix_product_integral {Ω I : Type*}
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω] [Fintype I] [DecidableEq I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → Matrix I I ℂ) (hK : Continuous K) :
    (∫ x,Matrix.trace (K x.1*K x.2.1*K x.2.2.1*K x.2.2.2) ∂fourReadoutLaw μ)=
      Matrix.trace ((∫ ω,K ω∂μ)^4) := by
  have h := fourReadout_tensor_trace_integral μ (fun _ : Fin 4 => K) (fun _ => hK)
    (wickTensorPermutationMatrix outputTraceCycle)
  simp_rw [outputTraceCycle_trace] at h
  simpa [fourRecordAt,pow_succ] using h

end CertificationGaussian
