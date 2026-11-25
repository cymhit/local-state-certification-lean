import CertificationGaussian.CombinedWickPermutation

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- Products in four separate record variables factor under the actual four-copy probability. -/
theorem fourReadout_product_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Fin 4 → Ω → ℂ) :
    (∫ x,∏ b : Fin 4,f b (fourRecordAt x b) ∂fourReadoutLaw μ) =
      ∏ b : Fin 4,∫ s,f b s ∂μ := by
  simp [fourReadoutLaw,fourRecordAt,Fin.prod_univ_succ]
  rw [integral_prod_mul (f 0) (fun x : Ω × (Ω × Ω) => f 1 x.1 * (f 2 x.2.1 * f 3 x.2.2)),
    integral_prod_mul (f 1) (fun x : Ω × Ω => f 2 x.1 * f 3 x.2),
    integral_prod_mul (f 2) (f 3)]

section CompactRecords
variable {Ω J : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [SecondCountableTopology Ω] [Fintype J] [DecidableEq J]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [SecondCountableTopology Ω] in
/-- Matrix entry evaluation commutes with the genuine Bochner average in the Euclidean operator norm. -/
theorem matrix_entry_integral (K : Ω → Matrix J J ℂ) (hK : Continuous K) (i j : J) :
    (∫ s,K s ∂μ) i j = ∫ s,K s i j ∂μ := by
  let L := (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap
  have hKi : Integrable K μ :=
    hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := L.integral_comp_comm hKi
  exact h.symm

/-- Multilinearity and independent complete records commute the true four-block tensor trace with averaging. -/
theorem fourReadout_tensor_trace_integral (K : Fin 4 → Ω → Matrix J J ℂ)
    (hK : ∀ b,Continuous (K b))
    (U : Matrix (Fin 4 → J) (Fin 4 → J) ℂ) :
    (∫ x,Matrix.trace (wickTensorMatrix (fun b => K b (fourRecordAt x b))*U) ∂fourReadoutLaw μ) =
      Matrix.trace (wickTensorMatrix (fun b => ∫ s,K b s ∂μ)*U) := by
  have hi (f : Ω × (Ω × (Ω × Ω)) → ℂ) (hf : Continuous f) :
      Integrable f (fourReadoutLaw μ) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,wickTensorMatrix]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const]
      apply congrArg (fun z : ℂ => z * U j i)
      calc
        _ = ∏ b : Fin 4, ∫ s, K b s (i b) (j b) ∂μ :=
          fourReadout_product_integral μ (fun b s => K b s (i b) (j b))
        _ = _ := by
          apply Finset.prod_congr rfl
          intro b _
          exact (matrix_entry_integral μ (K b) (hK b) (i b) (j b)).symm
    · intro j _
      apply hi
      fun_prop
  · intro i _
    apply hi
    fun_prop

end CompactRecords

/-- Scaling each of the four true block matrices gives the precise fourth power, including empty coordinates. -/
theorem wickTensorMatrix_four_real_smul {J : Type*} [Fintype J]
    (c : ℝ) (K : Fin 4 → Matrix J J ℂ) :
    wickTensorMatrix (fun b => c • K b)=(c^4:ℝ) • wickTensorMatrix K := by
  ext x y
  simp only [wickTensorMatrix,Matrix.smul_apply,Complex.real_smul,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,Complex.ofReal_pow]

theorem wickTensorMatrix_four_scaled_trace {J : Type*} [Fintype J] [DecidableEq J]
    (c : ℝ) (K : Fin 4 → Matrix J J ℂ)
    (U : Matrix (Fin 4 → J) (Fin 4 → J) ℂ) :
    Matrix.trace (wickTensorMatrix (fun b => c • K b)*U)=
      (c:ℂ)^4*Matrix.trace (wickTensorMatrix K*U) := by
  rw [wickTensorMatrix_four_real_smul,Matrix.smul_mul,Matrix.trace_smul]
  simp only [Complex.real_smul,Complex.ofReal_pow]

end CertificationGaussian
