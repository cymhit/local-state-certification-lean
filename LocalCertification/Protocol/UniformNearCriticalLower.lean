import LocalCertification.Quantum.MeasurableNearCriticalEvent
import LocalCertification.Protocol.NearCriticalBudgetRate

/-! A common-event lower bound for the closed two-threshold region of SM V.C.
The adjacent hard states use the same running calibration threshold. At
degree zero, the second state has a uniform maximally mixed background. -/

set_option autoImplicit false
open MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum
open LocalCertification.Extremal LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

private theorem zeroRateConstant_le_uniform {d : ℕ} (hd : 2 ≤ d) (b bmax : ℝ)
    (hb0 : 0 < b) (hu : b ≤ bmax) (hmax : bmax < 1) (C0 Cp : ℝ)
    (hC0 : 0 < C0) (hCp : 0 ≤ Cp) :
    zeroRateConstant d b C0 Cp ≤
      (4/(1-(bmax+(1-bmax)*((d : ℝ)+1)⁻¹))) * max C0 Cp := by
  have hq := qudit_parameter_gt_one hd
  have hi := inv_le_one_of_one_le₀ hq.le
  have hh := (zeroHighCoefficient_bounds hq (hb0.trans_le hu) hmax).2
  have hden : 1 - (bmax+(1-bmax)*((d:ℝ)+1)⁻¹) ≤ 1 - (b+(1-b)*((d:ℝ)+1)⁻¹) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hi)]
  have hsq : (1-b)^2 ≤ 1 := by nlinarith [mul_nonneg hb0.le (sub_nonneg.mpr (hu.trans hmax.le))]
  unfold zeroRateConstant
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr hh) hden
  · exact max_le_max le_rfl (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq hCp)
  · exact hC0.le.trans (le_max_left _ _)
  · exact div_nonneg (by norm_num) (sub_nonneg.mpr hh.le)

theorem nearCritical_lower_eventually_uniform (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (bmin bmax η : ℝ)
    (hmin : 0 < bmin) (hI : bmin ≤ bmax) (hmax : bmax < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ good : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1), IsCompact good ∧
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) goodᶜ ≤
        ENNReal.ofReal (measurableNearCriticalFailure d j n) ∧
      ∀ ψ ∈ good, ∀ b : ℝ, bmin ≤ b → b ≤ bmax → ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
        ENNReal.ofReal ((testingThreshold δ/C) * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2))) ≤
          ProductBudget.expectedBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ := by
  by_cases hj0 : j = 0
  · subst j
    change η < (1/2 : ℝ) * min (1-gamma ((d : ℝ)+1) 0)
      (gamma ((d : ℝ)+1) 0-gamma ((d : ℝ)+1) 1) at hwindow
    obtain ⟨C0,Cp,hC0,hCp,hevent⟩ := measurableNearCritical_zero_eventually_uniform.{u} hd bmin bmax hmin hI hmax
    let C := (4/(1-(bmax+(1-bmax)*((d : ℝ)+1)⁻¹))) * max C0 Cp
    have hh := (zeroHighCoefficient_bounds (qudit_parameter_gt_one hd) (hmin.trans_le hI) hmax).2
    have hC : 0 < C := mul_pos (div_pos (by norm_num) (sub_pos.mpr hh)) (hC0.trans_le (le_max_left _ _))
    refine ⟨C,hC,?_⟩
    filter_upwards [hevent,eventually_ge_atTop 1] with n hevent hn
    obtain ⟨hN,good,hcompact,hprob,hpair⟩ := hevent
    refine ⟨good,hcompact,hprob,?_⟩
    intro ψ hψ b hl hu ε hεl hεu δ hδ hhalf
    have hb0 := hmin.trans_le hl
    have hb1 := hu.trans_lt hmax
    obtain ⟨hlb,hinfo⟩ := hpair ψ hψ b hl hu
    have h := nearCritical_zero_product_lower_crossover hd hn (spherePureVector ψ) hN b η
      hb0 hb1 hη hwindow hlb C0 Cp hC0 (fun Ω _ M => (hinfo Ω M).1) (fun Ω _ M => (hinfo Ω M).2)
    have hc := zeroRateConstant_le_uniform hd b bmax hb0 hu hmax C0 Cp hC0 hCp.le
    have hTest := div_le_div_of_nonneg_left (testingThreshold_pos δ hδ hhalf).le h.1 hc
    calc
      _ ≤ ENNReal.ofReal ((testingThreshold δ / zeroRateConstant d b C0 Cp) *
          ((n:ℝ)^(0+1)/(1+(n:ℝ)*(max ε 0)^2))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hTest (by positivity))
      _ = _ := by congr 1; ring
      _ ≤ _ := (h.2 ε hεl hεu δ hδ hhalf).1
  · have hj : 1 ≤ j := by omega
    obtain ⟨Cj,Cp,hCj,hCp,hevent⟩ := measurableNearCritical_positive_eventually_uniform.{u} hd j hj bmin bmax hmin hI hmax
    let C := NearCriticalAdjacent.rateConstant hd j bmax Cj Cp
    have hC : 0 < C := NearCriticalAdjacent.rateConstant_pos hd j bmax hmax Cj Cp hCj
    refine ⟨C,hC,?_⟩
    filter_upwards [hevent,eventually_ge_atTop 1] with n hevent hn
    obtain ⟨hNj,hNp,good,hcompact,hprob,hpair⟩ := hevent
    refine ⟨good,hcompact,hprob,?_⟩
    intro ψ hψ b hl hu ε hεl hεu δ hδ hhalf
    have hb0 := hmin.trans_le hl
    have hb1 := hu.trans_lt hmax
    obtain ⟨hlj,hlp,hinfo⟩ := hpair ψ hψ b hl hu
    have h := nearCritical_product_lower_crossover hd j hj hn (spherePureVector ψ) hNj hNp b η
      hb0 hb1 hη hwindow hlj hlp Cj Cp hCj (fun Ω _ M => (hinfo Ω M).1) (fun Ω _ M => (hinfo Ω M).2)
    have hc : NearCriticalAdjacent.rateConstant hd j b Cj Cp ≤ C := by
      unfold C NearCriticalAdjacent.rateConstant
      apply mul_le_mul_of_nonneg_right _ (hCj.le.trans (le_max_left _ _))
      exact div_le_div_of_nonneg_left (by norm_num) (calibratedUniformWeight_pos hd j hmax)
        (calibratedUniformWeight_antitone hd j hu)
    have hTest := div_le_div_of_nonneg_left (testingThreshold_pos δ hδ hhalf).le h.1 hc
    calc
      _ ≤ ENNReal.ofReal ((testingThreshold δ / NearCriticalAdjacent.rateConstant hd j b Cj Cp) *
          ((n:ℝ)^(j+1)/(1+(n:ℝ)*(max ε 0)^2))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hTest (by positivity))
      _ = _ := by congr 1; ring
      _ ≤ _ := (h.2 ε hεl hεu δ hδ hhalf).1

end LocalCertification.Protocol.MeasurableExecution
