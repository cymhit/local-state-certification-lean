import CertificationGaussian.MeasurableFrameTail
import CertificationGaussian.TailAsymptotics

/-! # Uniform cubic tails for actual measurable matrix ensembles

The cutoff is chosen before the outcome space and its measure or matrix family.
The moment and frame identities are explicit inputs to this analytic lemma;
their actual product-POVM constructions are supplied separately. Signed kernel
weights and support at radius zero are allowed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace CertificationGaussian
universe u v

theorem measurableQuadraticEnsemble_eventually_cubic {d : Nat} (hd : 2 ≤ d)
    (J : Finset Nat) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : Nat in atTop, ∀ (Ω : Type u) (_ : MeasurableSpace Ω)
      (ν : Measure Ω) (_ : IsProbabilityMeasure ν)
      (B : Ω → Matrix (QuditIndex d n) (QuditIndex d n) ℂ),
      AEStronglyMeasurable B ν → (∀ᵐ s ∂ν, (B s).IsHermitian) →
      ∀ K : ℝ, 0 ≤ K → (∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K) →
      (∫ s, ((B s)^2).trace.re ∂ν) = kernelVarianceScale d n J θ →
      integralMatrixSecondMoment ν B =
        ((kernelVarianceScale d n J θ / ((d:ℝ)^n) : ℝ) : ℂ) • 1 →
      ‖integralMatrixFrame ν B‖ ≤ (kernelWeightL1 J θ)^2 / ((d:ℝ)^n) →
      (pairedGaussian (QuditIndex d n))
        {x | kernelVarianceScale d n J θ / n ≤
          |measurableQuadraticEnsemble ν B x-kernelVarianceScale d n J θ|} ≤
        ENNReal.ofReal (Real.exp (-(Real.log d / 4) * (n:ℝ)^3)) := by
  let c := kernelOrderLowerConstant d J θ hθ
  let s := effectiveKernelOrder J θ hθ
  let C := 5*Real.sqrt 8*kernelWeightL1 J θ/Real.sqrt c
  have hc : 0 < c := kernelOrderLowerConstant_pos hd J θ hθ
  have hL := kernelWeightL1_nonneg J θ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_polynomial_gaussian_cubic hd hC (s+5),
    eventually_ge_atTop (max 2 (2*J.sup id))] with n hbound hn
  intro Ω mΩ ν hν B hB hH K hK hBK htrace hsecond hframe
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hN : max 1 (2*J.sup id) ≤ n := by omega
  have hJ : ∀ k ∈ J, k ≤ n := by
    intro k hk
    have hk' : k ≤ J.sup id := Finset.le_sup (f := id) hk
    have ht := (le_max_right 2 (2*J.sup id)).trans hn
    omega
  have hv := (kernelVarianceScale_order_bounds hd J θ hθ hN).1
  have hv0 := kernelVarianceScale_pos hd J hJ θ hθ
  have hD : (0:ℝ) < (d:ℝ)^n := by positivity
  have hpref := relative_quartic_prefactor_le hc (show (1:ℝ) ≤ n by linarith) hD hL hv
  have hcard : (Fintype.card (QuditIndex d n):ℝ) = (d:ℝ)^n := by
    simp [QuditIndex]
  have htail := measurableQuadraticEnsemble_centered_abs_tail ν B hB hH hK hBK
    (kernelVarianceScale d n J θ) (kernelWeightL1 J θ) hv0.le
    (kernelVarianceScale_le_weight_sq hd J hJ θ) htrace
    (by simpa only [hcard] using hsecond) (by simpa only [hcard] using hframe)
    ((n:ℝ)^2) (by nlinarith) (kernelVarianceScale d n J θ/n) (by positivity)
  rw [hcard] at htail
  calc
    _ ≤ ENNReal.ofReal ((5*((n:ℝ)^2-1)^2 * Real.sqrt
        (8*(kernelWeightL1 J θ)^2*kernelVarianceScale d n J θ/(d:ℝ)^n) /
        (kernelVarianceScale d n J θ/n))^((n:ℝ)^2)) := htail
    _ ≤ ENNReal.ofReal ((C*(n:ℝ)^(s+5)/Real.sqrt ((d:ℝ)^n))^((n:ℝ)^2)) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow (by positivity) hpref (by positivity)
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

/-- The same Gaussian sample controls a finite family of actual ensembles. Each
index may have its own measurable outcome space and reference probability. -/
theorem measurableQuadraticEnsemble_eventually_finite_family_cubic {d : Nat} (hd : 2 ≤ d)
    (J : Finset Nat) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) (A : ℝ) :
    ∀ᶠ n : Nat in atTop, ∀ (ι : Type v) (Ω : ι → Type u)
      (_ : ∀ a, MeasurableSpace (Ω a)) (ν : ∀ a, Measure (Ω a))
      (_ : ∀ a, IsProbabilityMeasure (ν a))
      (B : ∀ a, Ω a → Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
      (K : ι → ℝ) (S : Finset ι),
      (∀ a ∈ S, AEStronglyMeasurable (B a) (ν a)) →
      (∀ a ∈ S, ∀ᵐ s ∂ν a, (B a s).IsHermitian) →
      (∀ a ∈ S, 0 ≤ K a) →
      (∀ a ∈ S, ∀ᵐ s ∂ν a, ‖matrixHilbertSchmidt (B a s)‖ ≤ K a) →
      (∀ a ∈ S, (∫ s, ((B a s)^2).trace.re ∂ν a) = kernelVarianceScale d n J θ) →
      (∀ a ∈ S, integralMatrixSecondMoment (ν a) (B a) =
        ((kernelVarianceScale d n J θ / ((d:ℝ)^n) : ℝ) : ℂ) • 1) →
      (∀ a ∈ S, ‖integralMatrixFrame (ν a) (B a)‖ ≤
        (kernelWeightL1 J θ)^2 / ((d:ℝ)^n)) →
      (S.card:ℝ) ≤ Real.exp (A*(n:ℝ)^2) →
      (pairedGaussian (QuditIndex d n))
        {x | ∃ a ∈ S, kernelVarianceScale d n J θ / n ≤
          |measurableQuadraticEnsemble (ν a) (B a) x-kernelVarianceScale d n J θ|} ≤
        ENNReal.ofReal (Real.exp (-(Real.log d / 8) * (n:ℝ)^3)) := by
  classical
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  have ha : 0 < Real.log d / 4 := div_pos (Real.log_pos hdR) (by norm_num)
  filter_upwards [measurableQuadraticEnsemble_eventually_cubic.{u} hd J θ hθ,
    eventually_quadratic_exp_mul_cubic ha A] with n hn hbound
  intro ι Ω mΩ ν hν B K S hB hH hK hBK htrace hsecond hframe hcard
  have he : {x | ∃ a ∈ S, kernelVarianceScale d n J θ / n ≤
        |measurableQuadraticEnsemble (ν a) (B a) x-kernelVarianceScale d n J θ|} =
      ⋃ a ∈ S, {x | kernelVarianceScale d n J θ / n ≤
        |measurableQuadraticEnsemble (ν a) (B a) x-kernelVarianceScale d n J θ|} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  rw [he]
  calc
    _ ≤ ∑ a ∈ S, (pairedGaussian (QuditIndex d n))
        {x | kernelVarianceScale d n J θ / n ≤
          |measurableQuadraticEnsemble (ν a) (B a) x-kernelVarianceScale d n J θ|} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ S, ENNReal.ofReal (Real.exp (-(Real.log d / 4) * (n:ℝ)^3)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact hn (Ω a) (mΩ a) (ν a) (hν a) (B a) (hB a ha) (hH a ha)
        (K a) (hK a ha) (hBK a ha) (htrace a ha) (hsecond a ha) (hframe a ha)
    _ = ENNReal.ofReal ((S.card:ℝ) * Real.exp (-(Real.log d / 4) * (n:ℝ)^3)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h := (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)).trans hbound
      convert h using 1
      congr 1
      ring

end CertificationGaussian
