import CertificationGaussian.GaussianRotation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CertificationGaussian

/-- Pulling a measurable density back commutes with pushing its measure forward. -/
theorem map_withDensity_comp {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (f : Ω → E) (hf : Measurable f) (ρ : E → ℝ≥0∞) (hρ : Measurable ρ) :
    (μ.withDensity (ρ ∘ f)).map f = (μ.map f).withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs hρ hf]
  rfl

variable (I : Type*) [Fintype I]

def gaussianProductDensity (x : I → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

@[fun_prop] theorem gaussianProductDensity_integrable : Integrable (gaussianProductDensity I) :=
  Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)

theorem gaussianProductDensity_nonneg (x : I → ℝ) : 0 ≤ gaussianProductDensity I x :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

/-- The finite product Gaussian has the product of its actual one-dimensional densities. -/
theorem productGaussian_eq_withDensity :
    Measure.pi (fun _ : I => gaussianReal 0 1) =
      (volume : Measure (I → ℝ)).withDensity (fun x => ENNReal.ofReal (gaussianProductDensity I x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (gaussianProductDensity_integrable I).restrict
      (Filter.Eventually.of_forall (gaussianProductDensity_nonneg I))]
  change ENNReal.ofReal (∫ x, gaussianProductDensity I x
    ∂(Measure.pi (fun _ : I => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  unfold gaussianProductDensity
  rw [integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_apply 0 (by norm_num) (s i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).restrict
    (Filter.Eventually.of_forall (gaussianPDFReal_nonneg 0 1))

/-- This expression depends only on the Euclidean radius. -/
def gaussianRadialDensity (m : Nat) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((Real.sqrt (2*Real.pi))⁻¹)^m * Real.exp (-r^2/2))

@[fun_prop] theorem gaussianRadialDensity_measurable (m : Nat) : Measurable (gaussianRadialDensity m) := by
  unfold gaussianRadialDensity
  fun_prop

theorem gaussianProductDensity_radial (x : I → ℝ) :
    ENNReal.ofReal (gaussianProductDensity I x) =
      gaussianRadialDensity (Fintype.card I) ‖(WithLp.toLp 2 x : EuclideanSpace ℝ I)‖ := by
  unfold gaussianProductDensity gaussianRadialDensity
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
    EuclideanSpace.real_norm_sq_eq]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- Actual standard Gaussian density relative to canonical Euclidean volume. -/
theorem stdGaussian_eq_radial_withDensity :
    stdGaussian (EuclideanSpace ℝ I) =
      (volume : Measure (EuclideanSpace ℝ I)).withDensity
        (fun x => gaussianRadialDensity (Fintype.card I) ‖x‖) := by
  rw [← map_pi_eq_stdGaussian, productGaussian_eq_withDensity]
  have he : (fun x : I → ℝ => ENNReal.ofReal (gaussianProductDensity I x)) =
      (fun x : EuclideanSpace ℝ I => gaussianRadialDensity (Fintype.card I) ‖x‖) ∘ WithLp.toLp 2 := by
    funext x
    exact gaussianProductDensity_radial I x
  rw [he, map_withDensity_comp _ _ (by fun_prop) _ (by fun_prop),
    (PiLp.volume_preserving_toLp I).map_eq]

theorem stdGaussian_zero_null [Nonempty I] :
    (stdGaussian (EuclideanSpace ℝ I)) {0} = 0 := by
  rw [stdGaussian_eq_radial_withDensity]
  exact measure_singleton 0

end CertificationGaussian
