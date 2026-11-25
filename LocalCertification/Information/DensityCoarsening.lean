import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Coarse-graining relative to a common reference probability

A measurable record map pushes forward both the reference measure and the two
Born laws. The coarse density difference is therefore the conditional mean of
the refined difference. We prove its squared-integral contraction by testing
this identity against the coarse difference and completing a square. This is
the conditional Jensen argument without any regular conditional probability
or standard Borel hypothesis. Relative entropy contracts under the same map.
-/

set_option autoImplicit false
open MeasureTheory InformationTheory
open scoped ENNReal
noncomputable section

namespace LocalCertification.Information.DensityCoarsening

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Pushforward of genuine density measures transports every measurable test. -/
theorem integral_density_test (ν : Measure X) (μ : Measure Y)
    (π : X → Y) (hπ : Measurable π) (f : X → ℝ) (g : Y → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfpos : ∀ x, 0 ≤ f x) (hgpos : ∀ y, 0 ≤ g y)
    (hpush : (ν.withDensity (fun x => ENNReal.ofReal (f x))).map π =
      μ.withDensity (fun y => ENNReal.ofReal (g y)))
    (k : Y → ℝ) (hk : Measurable k) :
    (∫ x, f x * k (π x) ∂ν) = ∫ y, g y * k y ∂μ := by
  have hν := integral_withDensity_eq_integral_toReal_smul
    hf.ennreal_ofReal (ae_of_all ν (fun _ => ENNReal.ofReal_lt_top)) (fun x => k (π x))
  have hμ := integral_withDensity_eq_integral_toReal_smul
    hg.ennreal_ofReal (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top)) k
  simp only [ENNReal.toReal_ofReal (hfpos _), smul_eq_mul] at hν
  simp only [ENNReal.toReal_ofReal (hgpos _), smul_eq_mul] at hμ
  rw [← hν, ← integral_map_of_stronglyMeasurable hπ hk.stronglyMeasurable, hpush]
  exact hμ

private theorem integrable_bounded (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x

/-- Completing a square proves the L2 contraction from its conditional-mean
test identity. The residual is measured on the original refined space. -/
theorem integral_sq_le_of_test (ν : Measure X) (μ : Measure Y)
    [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (π : X → Y) (hπ : Measurable π) (href : ν.map π = μ)
    (F : X → ℝ) (G : Y → ℝ) (hF : Measurable F) (hG : Measurable G)
    (B C : ℝ) (hB : ∀ x, |F x| ≤ B) (hC : ∀ y, |G y| ≤ C)
    (htest : (∫ x, F x * G (π x) ∂ν) = ∫ y, (G y)^2 ∂μ) :
    (∫ y, (G y)^2 ∂μ) ≤ ∫ x, (F x)^2 ∂ν := by
  have iF := integrable_bounded ν F hF B hB
  have iG := integrable_bounded ν (fun x => G (π x)) (hG.comp hπ) C (fun x => hC (π x))
  have bF : ∀ᵐ x ∂ν, ‖F x‖ ≤ B := ae_of_all _ fun x => by simpa using hB x
  have bG : ∀ᵐ x ∂ν, ‖G (π x)‖ ≤ C := ae_of_all _ fun x => by simpa using hC (π x)
  have iFF : Integrable (fun x => (F x)^2) ν := by
    simpa only [pow_two] using iF.mul_bdd hF.aestronglyMeasurable bF
  have iGG : Integrable (fun x => (G (π x))^2) ν := by
    simpa only [pow_two, Function.comp_apply] using
      iG.mul_bdd (hG.comp hπ).aestronglyMeasurable bG
  have iFG : Integrable (fun x => F x * G (π x)) ν :=
    iF.mul_bdd (hG.comp hπ).aestronglyMeasurable bG
  have hmap : (∫ x, (G (π x))^2 ∂ν) = ∫ y, (G y)^2 ∂μ := by
    rw [← integral_map_of_stronglyMeasurable hπ (hG.pow_const 2).stronglyMeasurable, href]
  have hid : (∫ x, (F x - G (π x))^2 ∂ν) =
      (∫ x, (F x)^2 ∂ν) - 2 * (∫ x, F x * G (π x) ∂ν) +
        ∫ x, (G (π x))^2 ∂ν := by
    calc
      _ = ∫ x, ((F x)^2 - 2 * (F x * G (π x)) + (G (π x))^2) ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring
      _ = _ := by
        have ha := integral_add (iFF.sub (iFG.const_mul 2)) iGG
        have hs := integral_sub iFF (iFG.const_mul 2)
        simp only [Pi.sub_apply] at ha hs
        rw [ha, hs, integral_const_mul]
  have hn : 0 ≤ ∫ x, (F x - G (π x))^2 ∂ν :=
    integral_nonneg (fun x => sq_nonneg (F x - G (π x)))
  rw [hid, htest, hmap] at hn
  linarith

/-- Squared reference-density difference contracts under a common record map.
The pushforward hypotheses concern the actual density measures, not merely
pointwise matrices or a formal renaming of outcomes. -/
theorem integral_difference_sq_le
    (ν : Measure X) (μ : Measure Y) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (π : X → Y) (hπ : Measurable π) (href : ν.map π = μ)
    (f₀ f₁ : X → ℝ) (g₀ g₁ : Y → ℝ)
    (hf₀ : Measurable f₀) (hf₁ : Measurable f₁)
    (hg₀ : Measurable g₀) (hg₁ : Measurable g₁)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbf₀ : ∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ C) (hbf₁ : ∀ x, 0 ≤ f₁ x ∧ f₁ x ≤ C)
    (hbg₀ : ∀ y, 0 ≤ g₀ y ∧ g₀ y ≤ C) (hbg₁ : ∀ y, 0 ≤ g₁ y ∧ g₁ y ≤ C)
    (hpush₀ : (ν.withDensity (fun x => ENNReal.ofReal (f₀ x))).map π =
      μ.withDensity (fun y => ENNReal.ofReal (g₀ y)))
    (hpush₁ : (ν.withDensity (fun x => ENNReal.ofReal (f₁ x))).map π =
      μ.withDensity (fun y => ENNReal.ofReal (g₁ y))) :
    (∫ y, (g₀ y - g₁ y)^2 ∂μ) ≤ ∫ x, (f₀ x - f₁ x)^2 ∂ν := by
  have hdiff : ∀ {a b : ℝ}, 0 ≤ a → a ≤ C → 0 ≤ b → b ≤ C → |a-b| ≤ C := by
    intro a b ha ha' hb hb'
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hG : Measurable (fun y => g₀ y-g₁ y) := hg₀.sub hg₁
  have hGb : ∀ y, |g₀ y-g₁ y| ≤ C := fun y =>
    hdiff (hbg₀ y).1 (hbg₀ y).2 (hbg₁ y).1 (hbg₁ y).2
  apply integral_sq_le_of_test ν μ π hπ href (fun x => f₀ x-f₁ x)
    (fun y => g₀ y-g₁ y) (hf₀.sub hf₁) hG C C
    (fun x => hdiff (hbf₀ x).1 (hbf₀ x).2 (hbf₁ x).1 (hbf₁ x).2) hGb
  have hi (f : X → ℝ) (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ C) :
      Integrable (fun x => f x * (g₀ (π x)-g₁ (π x))) ν :=
    (integrable_bounded ν f hf C (fun x => by rw [abs_of_nonneg (hb x).1]; exact (hb x).2)).mul_bdd
      (hG.comp hπ).aestronglyMeasurable (ae_of_all _ fun x => by simpa using hGb (π x))
  have hj (g : Y → ℝ) (hg : Measurable g) (hb : ∀ y, 0 ≤ g y ∧ g y ≤ C) :
      Integrable (fun y => g y * (g₀ y-g₁ y)) μ :=
    (integrable_bounded μ g hg C (fun y => by rw [abs_of_nonneg (hb y).1]; exact (hb y).2)).mul_bdd
      hG.aestronglyMeasurable (ae_of_all _ fun y => by simpa using hGb y)
  calc
    _ = (∫ x, f₀ x * (g₀ (π x)-g₁ (π x)) ∂ν) -
        ∫ x, f₁ x * (g₀ (π x)-g₁ (π x)) ∂ν := by
      simp_rw [sub_mul]
      exact integral_sub (hi f₀ hf₀ hbf₀) (hi f₁ hf₁ hbf₁)
    _ = (∫ y, g₀ y * (g₀ y-g₁ y) ∂μ) - ∫ y, g₁ y * (g₀ y-g₁ y) ∂μ := by
      rw [integral_density_test ν μ π hπ f₀ g₀ hf₀ hg₀ (fun x => (hbf₀ x).1)
        (fun y => (hbg₀ y).1) hpush₀ _ hG,
        integral_density_test ν μ π hπ f₁ g₁ hf₁ hg₁ (fun x => (hbf₁ x).1)
        (fun y => (hbg₁ y).1) hpush₁ _ hG]
    _ = ∫ y, (g₀ y-g₁ y)^2 ∂μ := by
      rw [← integral_sub (hj g₀ hg₀ hbg₀) (hj g₁ hg₁ hbg₁)]
      apply integral_congr_ae
      exact ae_of_all _ fun y => by ring

/-- The same retained-record map also contracts relative entropy. -/
theorem klDiv_coarsen_le (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : X → Y) (hπ : Measurable π) :
    klDiv (P.map π) (Q.map π) ≤ klDiv P Q :=
  klDiv_map_le P Q hπ

end LocalCertification.Information.DensityCoarsening
