import LocalCertification.Information.KLVariational
import LocalCertification.Information.KLVariationalConverse
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Variational information recursion for general probability kernels

A bounded measurable test on the joint record is integrated conditionally.
Its logarithmic partition function is again bounded and measurable, so the
variational entropy bounds apply to the marginal record. This proves the
one-step recursion in Supplemental Material Section V.A without restricting the measurable spaces.
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LocalCertification.Information

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The conditional logarithmic partition function of a real test. -/
noncomputable def kernelLogPartition (κ : Kernel α β) (f : α × β → ℝ) (a : α) : ℝ :=
  Real.log (∫ b, Real.exp (f (a, b)) ∂κ a)

theorem measurable_kernelLogPartition (κ : Kernel α β) [IsSFiniteKernel κ]
    {f : α × β → ℝ} (hf : Measurable f) : Measurable (kernelLogPartition κ f) := by
  exact Real.measurable_log.comp
    ((Real.measurable_exp.comp hf).stronglyMeasurable.integral_kernel_prod_right'
      (κ := κ)).measurable

theorem integrable_exp_of_measurable_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable (fun x => Real.exp (f x)) μ := by
  apply integrable_of_measurable_abs_le μ (Real.measurable_exp.comp hf) (Real.exp M)
  intro x
  change |Real.exp (f x)| ≤ Real.exp M
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (abs_le.mp (hM x)).2

/-- Integrating an exponential against a probability kernel preserves its
pointwise exponential bounds, hence the logarithmic test remains bounded. -/
theorem abs_kernelLogPartition_le (κ : Kernel α β) [IsMarkovKernel κ]
    {f : α × β → ℝ} (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (a : α) : |kernelLogPartition κ f a| ≤ M := by
  have hfi : Integrable (fun b => Real.exp (f (a, b))) (κ a) :=
    integrable_exp_of_measurable_abs_le (κ a) (hf.comp measurable_prodMk_left)
      M (fun b => hM (a, b))
  have hlo : Real.exp (-M) ≤ ∫ b, Real.exp (f (a, b)) ∂κ a := by
    calc
      _ = ∫ _ : β, Real.exp (-M) ∂κ a := by simp
      _ ≤ _ := integral_mono (integrable_const _) hfi fun b =>
        Real.exp_le_exp.mpr (abs_le.mp (hM (a, b))).1
  have hhi : (∫ b, Real.exp (f (a, b)) ∂κ a) ≤ Real.exp M := by
    calc
      _ ≤ ∫ _ : β, Real.exp M ∂κ a := integral_mono hfi (integrable_const _) fun b =>
        Real.exp_le_exp.mpr (abs_le.mp (hM (a, b))).2
      _ = _ := by simp
  have hzpos := (Real.exp_pos (-M)).trans_le hlo
  apply abs_le.mpr
  constructor
  · simpa only [kernelLogPartition, Real.log_exp] using Real.log_le_log (Real.exp_pos (-M)) hlo
  · simpa only [kernelLogPartition, Real.log_exp] using Real.log_le_log hzpos hhi

/-- Marginal relative entropy plus the expected pointwise information bound
controls the joint record. All outcome and history spaces are arbitrary
measurable spaces; the nonnegative step bound need only be integrable. -/
theorem klDiv_compProd_le_of_pointwise_bound
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (A : ℝ) (hA : 0 ≤ A) (hμν : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal A)
    (c : α → ℝ) (hc : Integrable c μ) (hcpos : ∀ x, 0 ≤ c x)
    (hstep : ∀ x, InformationTheory.klDiv (κ x) (η x) ≤ ENNReal.ofReal (c x)) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) ≤ ENNReal.ofReal (A + ∫ x, c x ∂μ) := by
  apply klDiv_le_of_bounded_variational
  intro f hf hbounded
  obtain ⟨M, hM⟩ := hbounded
  let g : α → ℝ := kernelLogPartition η f
  have hg : Measurable g := measurable_kernelLogPartition η hf
  have hgb : ∀ a, |g a| ≤ M := abs_kernelLogPartition_le η hf M hM
  have hgi : Integrable g μ := integrable_of_measurable_abs_le μ hg M hgb
  have hge : Integrable (fun x => Real.exp (g x)) ν :=
    integrable_exp_of_measurable_abs_le ν hg M hgb
  have hmarginal : (∫ x, g x ∂μ) - Real.log (∫ x, Real.exp (g x) ∂ν) ≤ A := by
    exact (ENNReal.ofReal_le_ofReal_iff hA).mp
      ((klDiv_variational_lower_bound μ ν g hgi hge).trans hμν)
  have hlocal : ∀ a, (∫ b, f (a, b) ∂κ a) ≤ c a + g a := by
    intro a
    have hfa : Integrable (fun b => f (a, b)) (κ a) :=
      integrable_of_measurable_abs_le (κ a) (hf.comp measurable_prodMk_left)
        M (fun b => hM (a, b))
    have hea : Integrable (fun b => Real.exp (f (a, b))) (η a) :=
      integrable_exp_of_measurable_abs_le (η a) (hf.comp measurable_prodMk_left)
        M (fun b => hM (a, b))
    have hv := (ENNReal.ofReal_le_ofReal_iff (hcpos a)).mp
      ((klDiv_variational_lower_bound (κ a) (η a) (fun b => f (a, b)) hfa hea).trans
        (hstep a))
    change (∫ b, f (a, b) ∂κ a) ≤ c a + Real.log (∫ b, Real.exp (f (a, b)) ∂η a)
    linarith
  have hmeanmeas : Measurable (fun a => ∫ b, f (a, b) ∂κ a) :=
    (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hmeanbound : ∀ a, |∫ b, f (a, b) ∂κ a| ≤ M := by
    intro a
    have hnorm := norm_integral_le_of_norm_le (μ := κ a) (f := fun b => f (a, b))
      (integrable_const M)
      (ae_of_all _ fun b => by simpa only [Real.norm_eq_abs] using hM (a, b))
    simpa using hnorm
  have hmeani := integrable_of_measurable_abs_le μ hmeanmeas M hmeanbound
  have hmean := integral_mono hmeani (hc.add hgi) hlocal
  simp only [Pi.add_apply] at hmean
  rw [integral_add hc hgi] at hmean
  have hjoint : Integrable f (μ ⊗ₘ κ) := integrable_of_measurable_abs_le _ hf M hM
  have hjointExp : Integrable (fun x => Real.exp (f x)) (ν ⊗ₘ η) :=
    integrable_exp_of_measurable_abs_le _ hf M hM
  have hpartition : (∫ x, Real.exp (g x) ∂ν) =
      ∫ x, Real.exp (f x) ∂(ν ⊗ₘ η) := by
    rw [Measure.integral_compProd hjointExp]
    apply integral_congr_ae
    apply ae_of_all
    intro a
    have hea := integrable_exp_of_measurable_abs_le (η a)
      (hf.comp measurable_prodMk_left) M (fun b => hM (a, b))
    exact Real.exp_log (integral_exp_pos hea)
  rw [hpartition] at hmarginal
  rw [Measure.integral_compProd hjoint]
  linarith

end LocalCertification.Information
