import LocalCertification.Probability.BlockAmplification

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LocalCertification.Comparisons

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The one-sided Hoeffding bound for actual independent bounded observations. -/
theorem iid_bounded_upper_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => μ)
      {x | (m : ℝ) * ((∫ z, f z ∂μ) + ε) ≤ ∑ i, f (x i)} ≤
      ENNReal.ofReal (Real.exp (-2 * (m : ℝ) * ε ^ 2)) := by
  let M := Measure.pi (fun _ : Fin m => μ)
  let X := fun (i : Fin m) (x : Fin m → Ω) => f (x i)
  let Y := fun (i : Fin m) (x : Fin m → Ω) => X i x - (∫ z, X i z ∂M)
  have hi : iIndepFun X M := iIndepFun_pi (fun _ => hf.aemeasurable)
  have hY : iIndepFun Y M := hi.comp (fun i y => y - (∫ z, X i z ∂M)) (by intro i; fun_prop)
  have hmean (i : Fin m) : (∫ x, X i x ∂M) = ∫ z, f z ∂μ := by
    have hp := measurePreserving_eval (fun _ : Fin m => μ) i
    have hfm : AEStronglyMeasurable f (M.map (fun x => x i)) := by
      rw [hp.map_eq]
      exact hf.aestronglyMeasurable
    change (∫ x, f (x i) ∂M) = _
    rw [← integral_map hp.measurable.aemeasurable hfm, hp.map_eq]
  have hc (i : Fin m) : HasSubgaussianMGF (Y i) (1 / 4) M := by
    have h := hasSubgaussianMGF_of_mem_Icc
      ((hf.comp (measurable_pi_apply i)).aemeasurable : AEMeasurable (X i) M)
      (Filter.Eventually.of_forall (fun x => hb (x i)))
    convert h using 1 <;> norm_num [Y, X]
  have hs := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY
    (s := Finset.univ) (c := fun _ => (1 / 4 : ℝ≥0)) (fun i _ => hc i)
    (ε := (m : ℝ) * ε) (mul_nonneg (Nat.cast_nonneg _) hε)
  have hsub : {x | (m : ℝ) * ((∫ z, f z ∂μ) + ε) ≤ ∑ i, f (x i)} ⊆
      {x | (m : ℝ) * ε ≤ ∑ i, Y i x} := by
    intro x hx
    change (m : ℝ) * ε ≤ ∑ i, (X i x - (∫ z, X i z ∂M))
    simp only [Finset.sum_sub_distrib, hmean, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    change (m : ℝ) * ((∫ z, f z ∂μ) + ε) ≤ ∑ i, f (x i) at hx
    dsimp only [X]
    nlinarith
  have hr := (measureReal_mono (μ := M) hsub).trans hs
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hexp : -((m : ℝ) * ε) ^ 2 / (2 * (↑(∑ _i : Fin m, (1 / 4 : ℝ≥0)) : ℝ)) =
      -2 * (m : ℝ) * ε ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    field_simp
    ring
  rw [hexp] at hr
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hr

theorem bounded_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
    exact (hb x).2)

/-- Lower tails use the complementary bounded outcome, with no positivity assumption on its mean. -/
theorem iid_bounded_lower_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => μ)
      {x | (∑ i, f (x i)) ≤ (m : ℝ) * ((∫ z, f z ∂μ) - ε)} ≤
      ENNReal.ofReal (Real.exp (-2 * (m : ℝ) * ε ^ 2)) := by
  have hg (x : Ω) : 1 - f x ∈ Set.Icc (0 : ℝ) 1 := by
    have h := hb x
    constructor <;> linarith [h.1, h.2]
  have h := iid_bounded_upper_tail μ (fun x => 1 - f x) (by fun_prop) hg hm hε
  have he : (∫ z, (1 - f z) ∂μ) = 1 - (∫ z, f z ∂μ) := by
    rw [integral_sub (integrable_const _) (bounded_integrable μ f hf hb)]
    simp
  rw [he] at h
  refine (measure_mono ?_).trans h
  intro x hx
  simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  change (∑ i, f (x i)) ≤ (m : ℝ) * ((∫ z, f z ∂μ) - ε) at hx
  nlinarith

end LocalCertification.Comparisons
