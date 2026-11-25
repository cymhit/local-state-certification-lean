import LocalCertification.Information.KLVariationalApproximation

/-!
# Relative entropy controlled by bounded measurable tests

Clipped logarithmic Radon--Nikodym densities recover the relative entropy by
Fatou's lemma, including infinite entropy. This argument imposes no countable
generation or standard Borel condition on the outcome space. It supplies the
converse variational step used in the general-record information recursion.
-/

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology

namespace LocalCertification.Information

theorem measurable_clippedLog (n : ℕ) : Measurable (clippedLog n) := by
  unfold clippedLog
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_const.max (measurable_const.min Real.measurable_log))

theorem integrable_of_measurable_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable f μ := by
  refine (integrable_const M).mono' hf.aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hM x

/-- An upper bound on every bounded measurable variational test bounds the full
relative entropy. Absolute continuity is explicit; finite entropy is not assumed. -/
theorem klDiv_le_of_bounded_variational_of_ac {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hAC : μ ≪ ν) (C : ℝ)
    (hbound : ∀ f : Ω → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      (∫ x, f x ∂μ) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ C) :
    InformationTheory.klDiv μ ν ≤ ENNReal.ofReal C := by
  let r : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal
  let f : ℕ → Ω → ℝ := fun n x => clippedLog n (r x)
  let g : ℕ → Ω → ℝ := fun n x => r x * f n x - Real.exp (f n x) + 1
  have hr : Measurable r := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hrpos : ∀ x, 0 ≤ r x := fun _ => ENNReal.toReal_nonneg
  have hf : ∀ n, Measurable (f n) := fun n => (measurable_clippedLog n).comp hr
  have hfbound : ∀ n x, |f n x| ≤ (n : ℝ) := fun n x => abs_clippedLog_le n (r x)
  have hfi : ∀ n, Integrable (f n) μ := fun n =>
    integrable_of_measurable_abs_le μ (hf n) n (hfbound n)
  have hei : ∀ n, Integrable (fun x => Real.exp (f n x)) ν := by
    intro n
    apply integrable_of_measurable_abs_le ν (Real.measurable_exp.comp (hf n)) (Real.exp n)
    intro x
    change |Real.exp (f n x)| ≤ Real.exp n
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (abs_le.mp (hfbound n x)).2
  have hg : ∀ n, Measurable (g n) := fun n =>
    ((hr.mul (hf n)).sub (Real.measurable_exp.comp (hf n))).add measurable_const
  have hgi : ∀ n, Integrable (g n) ν := by
    intro n
    exact ((integrable_toReal_rnDeriv_mul_iff hAC).mpr (hfi n)).sub (hei n)
      |>.add (integrable_const 1)
  have hgnonneg : ∀ n x, 0 ≤ g n x := fun n x =>
    clippedLog_entropy_nonneg n (r x) (hrpos x)
  have hgintegral : ∀ n, ∫ x, g n x ∂ν ≤ C := by
    intro n
    have hzlower : Real.exp (-(n : ℝ)) ≤ ∫ x, Real.exp (f n x) ∂ν := by
      calc
        _ = ∫ _ : Ω, Real.exp (-(n : ℝ)) ∂ν := by simp
        _ ≤ _ := integral_mono (integrable_const _) (hei n) fun x =>
          Real.exp_le_exp.mpr (abs_le.mp (hfbound n x)).1
    have hzpos : 0 < ∫ x, Real.exp (f n x) ∂ν :=
      (Real.exp_pos _).trans_le hzlower
    have hlog := Real.log_le_sub_one_of_pos hzpos
    have htest := hbound (f n) (hf n) ⟨n, hfbound n⟩
    have hmul : Integrable (fun x => r x * f n x) ν :=
      (integrable_toReal_rnDeriv_mul_iff hAC).mpr (hfi n)
    change (∫ x, ((fun x => r x * f n x) - (fun x => Real.exp (f n x))) x + 1 ∂ν) ≤ C
    rw [integral_add (hmul.sub (hei n)) (integrable_const 1)]
    simp only [Pi.sub_apply]
    rw [integral_sub hmul (hei n)]
    change (∫ x, (μ.rnDeriv ν x).toReal * f n x ∂ν) -
      (∫ x, Real.exp (f n x) ∂ν) + (∫ _ : Ω, (1 : ℝ) ∂ν) ≤ C
    rw [integral_toReal_rnDeriv_mul hAC]
    simp only [integral_const]
    simp
    linarith
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hAC]
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂ν := by
      apply lintegral_congr
      intro x
      have ht := (ENNReal.continuous_ofReal.tendsto _).comp
        (clippedLog_entropy_tendsto (r x) (hrpos x))
      exact ht.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂ν) atTop :=
      lintegral_liminf_le fun n => (hg n).ennreal_ofReal
    _ ≤ ENNReal.ofReal C := by
      apply liminf_le_of_frequently_le'
      apply Frequently.of_forall
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hgi n) (ae_of_all _ (hgnonneg n))]
      exact ENNReal.ofReal_le_ofReal (hgintegral n)

/-- Null-set indicator tests force absolute continuity whenever all bounded
variational objectives have a common finite upper bound. -/
theorem absolutelyContinuous_of_bounded_variational {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (C : ℝ)
    (hbound : ∀ f : Ω → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      (∫ x, f x ∂μ) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ C) : μ ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  by_contra hμs
  have hreal : μ.real s ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos hμs (measure_ne_top μ s)).ne'
  have htest : ∀ t : ℝ, t * μ.real s ≤ C := by
    intro t
    let f : Ω → ℝ := s.indicator (fun _ => t)
    have hf : Measurable f := measurable_const.indicator hs
    have hb : ∀ x, |f x| ≤ |t| := by
      intro x
      by_cases hx : x ∈ s <;> simp [f, hx]
    have hzero : f =ᵐ[ν] fun _ => 0 := by
      have hout : ∀ᵐ x ∂ν, x ∉ s := by simpa [ae_iff] using hνs
      filter_upwards [hout] with x hx
      simp [f, hx]
    have heq : (∫ x, Real.exp (f x) ∂ν) = 1 := by
      calc
        _ = ∫ _ : Ω, (1 : ℝ) ∂ν := integral_congr_ae
          (hzero.mono fun x hx => by simp [hx])
        _ = 1 := by simp
    have ht := hbound f hf ⟨|t|, hb⟩
    rw [heq, Real.log_one, sub_zero] at ht
    simpa [f, integral_indicator hs, setIntegral_const, smul_eq_mul, mul_comm] using ht
  have hbad := htest ((C + 1) / μ.real s)
  rw [div_mul_cancel₀ _ hreal] at hbad
  linarith

/-- Full converse variational inequality for probability measures on arbitrary
measurable spaces, with no absolute-continuity or finite-entropy hypothesis. -/
theorem klDiv_le_of_bounded_variational {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (C : ℝ)
    (hbound : ∀ f : Ω → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      (∫ x, f x ∂μ) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ C) :
    InformationTheory.klDiv μ ν ≤ ENNReal.ofReal C :=
  klDiv_le_of_bounded_variational_of_ac μ ν
    (absolutelyContinuous_of_bounded_variational μ ν C hbound) C hbound

end LocalCertification.Information
