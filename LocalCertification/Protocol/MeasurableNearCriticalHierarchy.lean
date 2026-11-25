import LocalCertification.Protocol.NearCriticalProductAssembly
import LocalCertification.Quantum.MeasurableNearCriticalEvent
import LocalCertification.Protocol.NearCriticalProductUpper
import LocalCertification.Protocol.UniformNearCriticalHierarchy
import LocalCertification.Information.ContinuousConfidenceRatio

/-! Corollary 2 and SM V.C (S105) for adaptive protocols with arbitrary
measurable local POVM outcomes. A single compact target family and cutoff
control the entire closed nearcritical window, on both the canonical sphere
and its actual complex-unitary Haar pullbacks. The exact testing-information
bound and its uniform fixed-confidence logarithmic form retain actual
expected budgets, maximum budgets, and feasible every-path integer caps. -/

set_option autoImplicit false
open MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum
open LocalCertification.Extremal LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

/-- Corollary 2 / SM V.C (S105) with the exact binary testing factor:
one target family and cutoff work throughout the closed epsilon window for
all confidence levels, including degree zero and actual Haar targets. -/
theorem qudit_nearCritical_product_hierarchy (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (b η : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    ∃ C Cupper : ℝ, 0 < C ∧ 0 < Cupper ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
        atTop (nhds 1) ∧
      (∀ n (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
        IsCompact {U : ComplexUnitary (QuditIndex d n) | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ good n} ∧
        complexUnitaryHaar (QuditIndex d n)
          {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ good n} =
          canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) ∧
      ∃ N : ℕ, 1 ≤ N ∧
      (∀ n : ℕ, N ≤ n → ∀ ψ ∈ good n,
        ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
        ENNReal.ofReal ((LocalCertification.Information.testingThreshold δ / C) * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2))) ≤
          ProductBudget.expectedBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ∧
        ProductBudget.expectedBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ≤
          ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) ∧
        ∃ m : ℕ, ProductBudget.capFeasible.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ m ∧
          (m : ℝ) ≤ Cupper * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ) ∧
          ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) ≤
            ENNReal.ofReal (Cupper * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ))) ∧
      (∀ n : ℕ, N ≤ n → ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
        ∀ U : ComplexUnitary (QuditIndex d n), complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ good n →
        ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
        ENNReal.ofReal ((LocalCertification.Information.testingThreshold δ / C) * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2))) ≤
          ProductBudget.expectedBudget.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ∧
        ProductBudget.expectedBudget.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ≤
          ENat.toENNReal (ProductBudget.maximumBudget.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) ∧
        ∃ m : ℕ, ProductBudget.capFeasible.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ m ∧
          (m : ℝ) ≤ Cupper * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ) ∧
          ENat.toENNReal (ProductBudget.maximumBudget.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) ≤
            ENNReal.ofReal (Cupper * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ))) := by
  obtain ⟨C, Cupper, hC, hCupper, good, htypical, N, hN, hall⟩ :=
    qudit_nearCritical_product_hierarchy_uniform.{u} d j hd b b η hb0 le_rfl hb1 hη hwindow
  refine ⟨C, Cupper, hC, hCupper, good, htypical.1, htypical.2.1, htypical.2.2, N, hN, ?_, ?_⟩
  · intro n hn ψ hψ
    exact hall n hn ψ hψ b le_rfl le_rfl
  · intro n hn ψ₀ U hU
    exact hall n hn (complexUnitarySphereAction (QuditIndex d n) U ψ₀) hU b le_rfl le_rfl

/-- Corollary 2 / SM V.C (S105) in uniform logarithmic form for general
measurable local POVMs. The same target family and cutoff precede the fixed
confidence cutoff; only the positive lower coefficient depends on it. -/
theorem qudit_nearCritical_product_confidence_hierarchy (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (b η : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) (hη : 0 < η)
    (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    ∃ Cupper : ℝ, 0 < Cupper ∧
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n, IsCompact (good n)) ∧
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n))
        atTop (nhds 1) ∧
      (∀ n (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
        IsCompact {U : ComplexUnitary (QuditIndex d n) | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ good n} ∧
        complexUnitaryHaar (QuditIndex d n)
          {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ good n} =
          canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)) ∧
      ∃ N : ℕ, 1 ≤ N ∧
      ∀ δstar : ℝ, 0 < δstar → δstar < 1/2 → ∃ c : ℝ, 0 < c ∧
      (∀ n : ℕ, N ≤ n → ∀ ψ ∈ good n,
        ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
        ENNReal.ofReal (c * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ)) ≤
          ProductBudget.expectedBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ∧
        ProductBudget.expectedBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ≤
          ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) ∧
        ∃ m : ℕ, ProductBudget.capFeasible.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ m ∧
          (m : ℝ) ≤ Cupper * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ) ∧
          ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) ≤
            ENNReal.ofReal (Cupper * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ))) ∧
      (∀ n : ℕ, N ≤ n → ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
        ∀ U : ComplexUnitary (QuditIndex d n), complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ good n →
        ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
        ENNReal.ofReal (c * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ)) ≤
          ProductBudget.expectedBudget.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ∧
        ProductBudget.expectedBudget.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ ≤
          ENat.toENNReal (ProductBudget.maximumBudget.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) ∧
        ∃ m : ℕ, ProductBudget.capFeasible.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ m ∧
          (m : ℝ) ≤ Cupper * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ) ∧
          ENat.toENNReal (ProductBudget.maximumBudget.{u} (haarPureVector ψ₀ U) (b+(1-b)*(gamma ((d : ℝ)+1) j+ε)) b δ) ≤
            ENNReal.ofReal (Cupper * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ))) := by
  obtain ⟨C,Cupper,hC,hCupper,good,hcompact,hprob,hhaar,N,hN,hsphere,hHaar⟩ :=
    qudit_nearCritical_product_hierarchy.{u} d j hd b η hb0 hb1 hη hwindow
  refine ⟨Cupper,hCupper,good,hcompact,hprob,hhaar,N,hN,?_⟩
  intro δstar hs0 hshalf
  obtain ⟨k, hk, hcompare⟩ := testingThreshold_confidence_lower_via_continuous_ratio δstar hs0 hshalf
  have scale_bound (n : ℕ) (ε δ : ℝ) (hδ : 0 < δ) (hcut : δ ≤ δstar) :
      (k/C) * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) * Real.log (1/δ) ≤
        (testingThreshold δ/C) * ((n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2)) := by
    have h := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hcompare δ hδ hcut) hC.le)
      (show 0 ≤ (n : ℝ)^(j+1)/(1+(n : ℝ)*(max ε 0)^2) by positivity)
    convert h using 1
    ring
  refine ⟨k/C, div_pos hk hC, ?_, ?_⟩
  · intro n hn ψ hψ ε hεl hεu δ hδ hcut
    obtain ⟨hlo,hmid,hcap⟩ := hsphere n hn ψ hψ ε hεl hεu δ hδ (hcut.trans_lt hshalf)
    exact ⟨(ENNReal.ofReal_le_ofReal
      (scale_bound n ε δ hδ hcut)).trans hlo,hmid,hcap⟩
  · intro n hn ψ₀ U hU ε hεl hεu δ hδ hcut
    obtain ⟨hlo,hmid,hcap⟩ := hHaar n hn ψ₀ U hU ε hεl hεu δ hδ (hcut.trans_lt hshalf)
    exact ⟨(ENNReal.ofReal_le_ofReal
      (scale_bound n ε δ hδ hcut)).trans hlo,hmid,hcap⟩

end LocalCertification.Protocol.MeasurableExecution
