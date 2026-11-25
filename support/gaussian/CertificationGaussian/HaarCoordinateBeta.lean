import CertificationGaussian.SphereCoordinatePowers
import CertificationGaussian.OverlapBetaMoments
import Mathlib.Probability.Moments.MGFAnalytic

/-! # Beta law of the squared modulus of a Haar coordinate -/

noncomputable section
open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped Topology
namespace CertificationGaussian

private theorem betaOne_integer_moment (m k : ℕ) :
    ∫ x : ℝ, x^k ∂betaMeasure 1 ((m : ℝ)+1) =
      (k.factorial : ℝ) / ((m+2).ascFactorial k : ℝ) := by
  rw [betaOne_moment k _ (by positivity)]
  unfold beta
  rw [show (k : ℝ)+1 + (m+1) = ((m+1+k : ℕ) : ℝ)+1 by push_cast; ring,
    show (1 : ℝ)+((m : ℝ)+1) = ((m+1 : ℕ) : ℝ)+1 by push_cast; ring]
  simp only [Real.Gamma_nat_eq_factorial, Real.Gamma_one, one_mul]
  rw [← Nat.factorial_mul_ascFactorial (m+1) k]
  push_cast
  field_simp

private theorem allExp_of_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (hb : ∀ᵐ x ∂μ, |X x| ≤ 1) :
    integrableExpSet X μ = univ := by
  apply eq_univ_of_forall
  intro t
  apply (integrable_const (Real.exp |t|)).mono' (by fun_prop)
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * X x ≤ |t * X x| := le_abs_self _
    _ = |t| * |X x| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = |t| := mul_one _

/-- On the unit interval the moments determine the law: the two bounded
variables have entire moment generating functions with the same Taylor series. -/
private theorem map_eq_of_bounded_moments {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hx : ∀ᵐ x ∂μ, |X x| ≤ 1) (hy : ∀ᵐ y ∂ν, |Y y| ≤ 1)
    (hm : ∀ k : ℕ, (∫ x, X x ^ k ∂μ) = (∫ y, Y y ^ k ∂ν)) :
    μ.map X = ν.map Y := by
  have hE := allExp_of_bounded μ X hX hx
  have hF := allExp_of_bounded ν Y hY hy
  have H (t : ℝ) : t ∈ interior (integrableExpSet X μ) := by simp [hE]
  have K (t : ℝ) : t ∈ interior (integrableExpSet Y ν) := by simp [hF]
  have AX : AnalyticOnNhd ℝ (mgf X μ) univ := fun t _ => analyticAt_mgf (H t)
  have AY : AnalyticOnNhd ℝ (mgf Y ν) univ := fun t _ => analyticAt_mgf (K t)
  have hxsum := (hasFPowerSeriesAt_mgf (H 0)).eventually_hasSum_sub
  have hysum := (hasFPowerSeriesAt_mgf (K 0)).eventually_hasSum_sub
  simp only [zero_mul, Real.exp_zero, mul_one] at hxsum hysum
  simp_rw [hm] at hxsum
  have hmgf : mgf X μ = mgf Y ν := AX.eq_of_eventuallyEq AY (z₀ := 0) (by
    filter_upwards [hxsum, hysum] with t tx ty using tx.unique ty)
  exact Measure.ext_of_complexMGF_eq hX.aemeasurable hY.aemeasurable
    (funext fun z => eqOn_complexMGF_of_mgf hmgf (H z.re))

private theorem beta_support_abs (b : ℝ) : ∀ᵐ x ∂betaMeasure 1 b, |x| ≤ 1 := by
  rw [betaMeasure, ae_withDensity_iff (show Measurable (betaPDF 1 b) from
    (measurable_betaPDFReal 1 b).ennreal_ofReal)]
  refine .of_forall fun x hx => ?_
  by_cases h : 0 < x ∧ x < 1
  · rw [abs_of_pos h.1]
    exact h.2.le
  · exact (hx (by simp [betaPDF_eq, h])).elim

/-- In complex dimension d≥2, a squared coordinate of a uniform sphere vector
has the Beta(1,d−1) distribution. -/
theorem haar_squaredCoordinate_beta (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I]
    (hd : 2 ≤ Fintype.card I) (i : I) :
    (canonicalSphereMeasure (EuclideanSpace ℂ I)).map
        (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 => ‖ψ.val i‖^2) =
      betaMeasure 1 ((Fintype.card I : ℝ)-1) := by
  let m := Fintype.card I - 2
  have hd' : Fintype.card I = m+2 := by dsimp [m]; omega
  have hb : (Fintype.card I : ℝ)-1 = (m : ℝ)+1 := by rw [hd']; push_cast; ring
  rw [hb]
  let _ := isProbabilityMeasureBeta zero_lt_one (show (0:ℝ)<m+1 by positivity)
  rw [← Measure.map_id (μ := betaMeasure 1 ((m : ℝ)+1))]
  refine map_eq_of_bounded_moments _ _ _ id (by fun_prop) measurable_id ?_ (beta_support_abs _) ?_
  · refine .of_forall fun ψ => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    have hcoord := norm_inner_le_norm (𝕜 := ℂ) (EuclideanSpace.basisFun I ℂ i) ψ.val
    simp only [EuclideanSpace.basisFun_inner, (EuclideanSpace.basisFun I ℂ).orthonormal.norm_eq_one i,
      mem_sphere_zero_iff_norm.mp ψ.property, one_mul] at hcoord
    nlinarith [norm_nonneg (ψ.val i)]
  · intro k
    rw [complexSphere_squaredCoordinate_moment, hd', ← betaOne_integer_moment]
    rfl

end CertificationGaussian

