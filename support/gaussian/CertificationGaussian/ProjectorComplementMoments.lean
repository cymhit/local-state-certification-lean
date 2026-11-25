import CertificationGaussian.ProjectorComplementKernel
import CertificationGaussian.MeasurableGaussianFrameBound

/-! # Genuine product-probability moments of complement kernels

Product outcomes may be arbitrary measurable spaces. Matrix Bochner integrability
is derived from scalar entry integrability, and product moments use actual Fubini.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

private def momentEntry {I : Type*} [Fintype I] [DecidableEq I] (i j : I) : Matrix I I ℂ →L[ℝ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

private def entriesMatrix {I : Type*} [Fintype I] [DecidableEq I] : (I → I → ℂ) →L[ℝ] Matrix I I ℂ where
  toFun A := A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_id

theorem matrix_integrable_of_entries {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (μ : Measure Ω) (F : Ω → Matrix I I ℂ)
    (hf : ∀ i j, Integrable (fun ω => F ω i j) μ) : Integrable F μ := by
  have h : Integrable (fun ω i j => F ω i j) μ :=
    Integrable.of_eval fun i => Integrable.of_eval (hf i)
  exact entriesMatrix.integrable_comp h

theorem matrix_entry_integral_of_integrable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (μ : Measure Ω) (F : Ω → Matrix I I ℂ) (hf : Integrable F μ) (i j : I) :
    (∫ ω, F ω ∂μ) i j = ∫ ω, F ω i j ∂μ :=
  ((momentEntry i j).integral_comp_comm hf).symm

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]
  {Ω : S → Type*} [∀ s, MeasurableSpace (Ω s)]
  (ν : (s : S) → Measure (Ω s)) [∀ s, IsProbabilityMeasure (ν s)]

theorem wickTensorMatrix_integrable (A : (s : S) → Ω s → Matrix I I ℂ)
    (hA : ∀ s, Integrable (A s) (ν s)) :
    Integrable (fun ω : (s : S) → Ω s => wickTensorMatrix (fun s => A s (ω s))) (Measure.pi ν) := by
  apply matrix_integrable_of_entries
  intro x y
  exact Integrable.fintype_prod_dep fun s => (momentEntry (x s) (y s)).integrable_comp (hA s)

theorem integral_wickTensorMatrix (A : (s : S) → Ω s → Matrix I I ℂ)
    (hA : ∀ s, Integrable (A s) (ν s)) :
    (∫ ω : (s : S) → Ω s, wickTensorMatrix (fun s => A s (ω s)) ∂Measure.pi ν) =
      wickTensorMatrix (fun s => ∫ t, A s t ∂ν s) := by
  ext x y
  rw [matrix_entry_integral_of_integrable _ _ (wickTensorMatrix_integrable ν A hA)]
  simp only [wickTensorMatrix, matrix_entry_integral_of_integrable _ _ (hA _)]
  exact integral_fintype_prod_eq_prod (fun s t => A s t (x s) (y s))

theorem measurableProjector_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : X → Matrix I I ℂ)
    (hm : AEStronglyMeasurable P μ) (hh : ∀ᵐ s ∂μ, (P s).IsHermitian)
    (hp : ∀ᵐ s ∂μ, P s * P s = P s) (ht : ∀ᵐ s ∂μ, (P s).trace = 1) :
    Integrable P μ := by
  have hb : ∀ᵐ s ∂μ, ‖matrixHilbertSchmidt (P s)‖ ≤ 1 := by
    filter_upwards [hh, hp, ht] with s hsH hsP hsT
    have he := matrixHilbertSchmidt_norm_sq (P s) hsH
    rw [pow_two (P s), hsP, hsT, Complex.one_re] at he
    nlinarith [norm_nonneg (matrixHilbertSchmidt (P s))]
  exact measurableMatrix_continuous_integrable μ P hm hb id continuous_id

omit [DecidableEq S] [Fintype I] in
theorem wickTensorMatrix_scalar_one (c : S → ℂ) :
    wickTensorMatrix (fun s => c s • (1 : Matrix I I ℂ)) =
      (∏ s, c s) • (1 : Matrix (S → I) (S → I) ℂ) := by
  classical
  ext x y
  simp only [wickTensorMatrix, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Matrix.one_apply, Fintype.prod_ite_zero, Finset.prod_const_one, ← funext_iff]

theorem projectorSubsetFactor_integrable (P : (s : S) → Ω s → Matrix I I ℂ)
    (hP : ∀ s, Integrable (P s) (ν s)) (A : Finset S) :
    Integrable (fun ω : (s : S) → Ω s => projectorSubsetFactor (fun s => P s (ω s)) A)
      (Measure.pi ν) := by
  unfold projectorSubsetFactor
  apply wickTensorMatrix_integrable ν (fun s t => if s ∈ A then 1 - P s t else P s t)
  intro s
  by_cases hs : s ∈ A
  · simp only [hs, ite_true]
    exact (integrable_const _).sub (hP s)
  · simpa only [hs, ite_false] using hP s

theorem projectorSubsetFactor_integral_scalar (P : (s : S) → Ω s → Matrix I I ℂ)
    (hP : ∀ s, Integrable (P s) (ν s)) (c : ℂ)
    (hmean : ∀ s, (∫ t, P s t ∂ν s) = c • (1 : Matrix I I ℂ)) (A : Finset S) :
    (∫ ω : (s : S) → Ω s, projectorSubsetFactor (fun s => P s (ω s)) A ∂Measure.pi ν) =
      (∏ s, if s ∈ A then 1-c else c) • (1 : Matrix (S → I) (S → I) ℂ) := by
  have hi (s : S) : Integrable (fun t => if s ∈ A then 1 - P s t else P s t) (ν s) := by
    by_cases hs : s ∈ A
    · simp only [hs, ite_true]
      exact (integrable_const _).sub (hP s)
    · simpa only [hs, ite_false] using hP s
  unfold projectorSubsetFactor
  rw [integral_wickTensorMatrix ν _ hi]
  have he (s : S) : (∫ t, (if s ∈ A then 1 - P s t else P s t) ∂ν s) =
      (if s ∈ A then 1-c else c) • (1 : Matrix I I ℂ) := by
    by_cases hs : s ∈ A
    · simp only [hs, ite_true]
      rw [integral_sub (integrable_const _) (hP s), hmean]
      simp [sub_smul]
    · simpa only [hs, ite_false] using hmean s
  simp_rw [he]
  exact wickTensorMatrix_scalar_one _

theorem projectorSubsetFactor_integral (P : (s : S) → Ω s → Matrix I I ℂ)
    (hP : ∀ s, Integrable (P s) (ν s)) (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, P s t ∂ν s) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (A : Finset S) :
    (∫ ω : (s : S) → Ω s, projectorSubsetFactor (fun s => P s (ω s)) A ∂Measure.pi ν) =
      (((Fintype.card I : ℂ)-1)^A.card / (Fintype.card I : ℂ)^(Fintype.card S)) •
        (1 : Matrix (S → I) (S → I) ℂ) := by
  rw [projectorSubsetFactor_integral_scalar ν P hP _ hmean A]
  have hd0 : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card I ≠ 0)
  have he (s : S) : (if s ∈ A then 1-(Fintype.card I : ℂ)⁻¹ else (Fintype.card I : ℂ)⁻¹) =
      (if s ∈ A then (Fintype.card I : ℂ)-1 else 1) / (Fintype.card I : ℂ) := by
    split_ifs <;> field_simp
  simp_rw [he]
  rw [Finset.prod_div_distrib]
  simp

theorem signedProjectorComplementKernel_integrable {J : Type*} [Fintype J]
    (P : (s : S) → Ω s → Matrix I I ℂ) (hP : ∀ s, Integrable (P s) (ν s))
    (A : J → Finset S) (c : J → ℝ) :
    Integrable (fun ω : (s : S) → Ω s => signedProjectorComplementKernel (fun s => P s (ω s)) A c)
      (Measure.pi ν) := by
  unfold signedProjectorComplementKernel
  exact integrable_finsetSum _ fun j _ => (projectorSubsetFactor_integrable ν P hP (A j)).smul (c j : ℂ)

theorem signedProjectorComplementKernel_integral {J : Type*} [Fintype J]
    (P : (s : S) → Ω s → Matrix I I ℂ) (hP : ∀ s, Integrable (P s) (ν s))
    (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, P s t ∂ν s) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (A : J → Finset S) (c : J → ℝ) :
    (∫ ω : (s : S) → Ω s, signedProjectorComplementKernel (fun s => P s (ω s)) A c ∂Measure.pi ν) =
      ((∑ j, (c j : ℂ) * ((Fintype.card I : ℂ)-1)^(A j).card) /
        (Fintype.card I : ℂ)^(Fintype.card S)) • (1 : Matrix (S → I) (S → I) ℂ) := by
  unfold signedProjectorComplementKernel
  have hi (j : J) : Integrable
      (fun ω : (s : S) → Ω s => (c j : ℂ) • projectorSubsetFactor (fun s => P s (ω s)) (A j))
      (Measure.pi ν) := (projectorSubsetFactor_integrable ν P hP (A j)).smul (c j : ℂ)
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  simp_rw [integral_smul, projectorSubsetFactor_integral ν P hP hd hmean, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem signedProjectorComplementKernel_integral_square {J : Type*} [Fintype J]
    (P : (s : S) → Ω s → Matrix I I ℂ) (hP : ∀ s, Integrable (P s) (ν s))
    (hp : ∀ s t, P s t * P s t = P s t) (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, P s t ∂ν s) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (A : J → Finset S) (hA : Function.Injective A) (c : J → ℝ) :
    (∫ ω : (s : S) → Ω s, (signedProjectorComplementKernel (fun s => P s (ω s)) A c)^2 ∂Measure.pi ν) =
      ((∑ j, (((c j)^2 : ℝ) : ℂ) * ((Fintype.card I : ℂ)-1)^(A j).card) /
        (Fintype.card I : ℂ)^(Fintype.card S)) • (1 : Matrix (S → I) (S → I) ℂ) := by
  have he (ω : (s : S) → Ω s) := signedProjectorComplementKernel_square
    (fun s => P s (ω s)) (fun s => hp s (ω s)) A hA c
  simp_rw [he]
  exact signedProjectorComplementKernel_integral ν P hP hd hmean A (fun j => (c j)^2)

/-- First and second moments of the actual signed kernel, with integrability derived. -/
theorem measurableProjector_signed_kernel_moments {J : Type*} [Fintype J]
    (P : (s : S) → Ω s → Matrix I I ℂ) (hm : ∀ s, AEStronglyMeasurable (P s) (ν s))
    (hh : ∀ s t, (P s t).IsHermitian) (hp : ∀ s t, P s t * P s t = P s t)
    (ht : ∀ s t, (P s t).trace = 1) (hd : 2 ≤ Fintype.card I)
    (hmean : ∀ s, (∫ t, P s t ∂ν s) = (Fintype.card I : ℂ)⁻¹ • (1 : Matrix I I ℂ))
    (A : J → Finset S) (hA : Function.Injective A) (c : J → ℝ) :
    (∫ ω : (s : S) → Ω s, signedProjectorComplementKernel (fun s => P s (ω s)) A c ∂Measure.pi ν) =
      ((∑ j, (c j : ℂ) * ((Fintype.card I : ℂ)-1)^(A j).card) /
        (Fintype.card I : ℂ)^(Fintype.card S)) • (1 : Matrix (S → I) (S → I) ℂ) ∧
    (∫ ω : (s : S) → Ω s, (signedProjectorComplementKernel (fun s => P s (ω s)) A c)^2 ∂Measure.pi ν) =
      ((∑ j, (((c j)^2 : ℝ) : ℂ) * ((Fintype.card I : ℂ)-1)^(A j).card) /
        (Fintype.card I : ℂ)^(Fintype.card S)) • (1 : Matrix (S → I) (S → I) ℂ) := by
  have hi (s : S) := measurableProjector_integrable (ν s) (P s) (hm s)
    (Filter.Eventually.of_forall (hh s)) (Filter.Eventually.of_forall (hp s)) (Filter.Eventually.of_forall (ht s))
  exact ⟨signedProjectorComplementKernel_integral ν P hi hd hmean A c,
    signedProjectorComplementKernel_integral_square ν P hi hp hd hmean A hA c⟩

end CertificationGaussian
