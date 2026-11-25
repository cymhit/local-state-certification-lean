import LocalCertification.Quantum.BornMeasure
import LocalCertification.Quantum.HaarProductBasis
import LocalCertification.Information.SingularFiniteKL

set_option autoImplicit false
open scoped BigOperators ENNReal
open Matrix MeasureTheory ProbabilityTheory InformationTheory Classical
noncomputable section
namespace LocalCertification.Quantum

/-- Actual mixed-state Born probability is continuous in the full product-unitary setting. -/
theorem productBorn_continuous (d n : ℕ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (x : CertificationGaussian.QuditIndex d n) :
    Continuous (fun U : Fin n → CertificationGaussian.LocalUnitary d => productBorn d n U ρ x) := by
  change Continuous (fun U => basisBorn
    ⟨CertificationGaussian.tensorUnitaryMatrix d n U,CertificationGaussian.tensorUnitaryMatrix_unitary d n U⟩ ρ x)
  simp_rw [basisBorn_diagonal]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,CertificationGaussian.tensorUnitaryMatrix]
  have he (i : Fin n) (a b : Fin d) : Continuous
      (fun U : Fin n → CertificationGaussian.LocalUnitary d => (U i).val a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp ((continuous_subtype_val : Continuous (fun V : CertificationGaussian.LocalUnitary d => V.val)).comp (continuous_apply i)))
  have hp (j : CertificationGaussian.QuditIndex d n) : Continuous
      (fun U : Fin n → CertificationGaussian.LocalUnitary d => ∏ i, (U i).val (j i) (x i)) :=
    continuous_finsetProd _ (fun i _ => he i (j i) (x i))
  exact Complex.continuous_re.comp (continuous_finsetSum _ (fun j _ =>
    (continuous_finsetSum _ (fun k _ => (hp k).star.mul continuous_const)).mul (hp j)))

/-- Exact finite-set probabilities of the existing physical readout measure. -/
theorem productBornMeasure_apply (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (s : Set (CertificationGaussian.QuditIndex d n)) :
    productBornMeasure d n U ρ s = ∑ x, if x ∈ s then ENNReal.ofReal (productBorn d n U ρ x) else 0 := by
  classical
  unfold productBornMeasure povmBornMeasure
  rw [PMF.toMeasure_apply _ (s.to_countable.measurableSet),tsum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ s <;> simp [hx,povmBornPMF,productBorn]

/-- The genuine state-dependent Born Markov kernel on all continuous product settings. -/
def productBornKernel (d n : ℕ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    Kernel (Fin n → CertificationGaussian.LocalUnitary d) (CertificationGaussian.QuditIndex d n) where
  toFun U := productBornMeasure d n U ρ
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s _
    simp_rw [productBornMeasure_apply]
    apply Finset.measurable_sum
    intro x _
    by_cases hx : x ∈ s
    · simpa only [ite_eq_left hx] using (productBorn_continuous d n ρ x).measurable.ennreal_ofReal
    · simp only [ite_eq_right hx]
      exact measurable_const

instance productBornKernel_markov (d n : ℕ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    IsMarkovKernel (productBornKernel d n ρ) := ⟨fun U => productBornMeasure_probability d n U ρ⟩

@[simp] theorem productBornKernel_apply (d n : ℕ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (U : Fin n → CertificationGaussian.LocalUnitary d) :
    productBornKernel d n ρ U = productBornMeasure d n U ρ := rfl

variable {H : Type*} [MeasurableSpace H]

/-- Arbitrary measurable histories choose one complete setting before consuming the next copy. -/
def controlledProductBornKernel (d n : ℕ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting) :
    Kernel H (CertificationGaussian.QuditIndex d n) := (productBornKernel d n ρ).comap setting hm

instance controlledProductBornKernel_markov (d n : ℕ) (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting) :
    IsMarkovKernel (controlledProductBornKernel d n ρ setting hm) := by
  unfold controlledProductBornKernel
  infer_instance

@[simp] theorem controlledProductBornKernel_apply (d n : ℕ)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (setting : H → Fin n → CertificationGaussian.LocalUnitary d)
    (hm : Measurable setting) (h : H) :
    controlledProductBornKernel d n ρ setting hm h = productBornMeasure d n (setting h) ρ := rfl

/-- Actual one-copy KL passes through any common measurable controller, without restricting history. -/
theorem controlledProductBornKernel_joint_kl_le (d n : ℕ)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ] (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) :
    klDiv (μ ⊗ₘ controlledProductBornKernel d n ρ setting hm)
      (μ ⊗ₘ controlledProductBornKernel d n σ setting hm) ≤ L := by
  rw [LocalCertification.Information.joint_klDiv_eq_lintegral_full]
  calc
    _ ≤ ∫⁻ _ : H, L ∂μ := lintegral_mono (fun h => hL (setting h))
    _ = L := by simp

end LocalCertification.Quantum
