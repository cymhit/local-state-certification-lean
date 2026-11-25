import LocalCertification.Paper
import LocalCertification.Protocol.NearCriticalNeighborhood
import LocalCertification.Protocol.MeasurableNearCriticalHierarchy
import LocalCertification.Protocol.NearCriticalProductUpper
import LocalCertification.Protocol.NearCriticalBudgetRate

open MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum
open LocalCertification.Extremal LocalCertification.Protocol.MeasurableExecution
open scoped ENNReal Topology
noncomputable section
namespace FixedBaselineChecks
universe u
example (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (b η : ℝ)
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
  exact LocalCertification.Paper.near_critical_testing_bounds d j hd b η hb0 hb1 hη hwindow

example (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (b η : ℝ)
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
  exact LocalCertification.Paper.near_critical_transition d j hd b η hb0 hb1 hη hwindow

end FixedBaselineChecks

namespace MovingThresholdChecks
universe u

/-- A consumer can choose both threshold sequences after obtaining the common witnesses. -/
example (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (a₀ b₀ δ : ℝ)
    (hb₀ : 0 < b₀) (hb₁ : b₀ < 1) (hδ : 0 < δ) (hh : δ < 1/2)
    (hcenter : (a₀-b₀)/(1-b₀) = gamma ((d:ℝ)+1) j) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (a₀,b₀) ∈ U ∧
    ∃ L H : ℝ, 0 < L ∧ 0 < H ∧
    ∃ G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      CompactHaarTypical d G ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ (a b : ℕ → ℝ), (∀ n, N ≤ n → (a n,b n) ∈ U) →
      ∀ n, N ≤ n → ∀ ψ ∈ G n,
        NearCriticalBudgetBounds.{u} (spherePureVector ψ) (a n) (b n) δ
          (L * nearCriticalCostOrder n j (criticalExcess d j (a n,b n)))
          (H * nearCriticalCostOrder n j (criticalExcess d j (a n,b n))) := by
  obtain ⟨U, ho, hc, _, L, H, hL, hH, G, hG, N, hN, hall⟩ :=
    qudit_nearCritical_product_neighborhood.{u} d j hd a₀ b₀ δ hb₀ hb₁ hcenter hδ hh
  exact ⟨U, ho, hc, L, H, hL, hH, G, hG, N, hN,
    fun a b hab n hn ψ hψ => hall n hn ψ hψ (a n,b n) (hab n hn)⟩

/-- The same pointwise budget guarantee includes both parameter endpoints
and equality at the critical value. -/
example (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (l h η δ : ℝ)
    (hl : 0 < l) (hlh : l ≤ h) (hh : h < 1) (hη : 0 < η) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (hw : η < (1/2:ℝ) * min
      ((if j = 0 then 1 else gamma ((d:ℝ)+1) (j-1)) - gamma ((d:ℝ)+1) j)
      (gamma ((d:ℝ)+1) j - gamma ((d:ℝ)+1) (j+1))) :
    ∃ C Cu : ℝ, 0 < C ∧ 0 < Cu ∧
    ∃ G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      CompactHaarTypical d G ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ ψ ∈ G n,
      let B := fun (b ε : ℝ) => NearCriticalBudgetBounds.{u} (spherePureVector ψ)
        (b+(1-b)*(gamma ((d:ℝ)+1) j+ε)) b δ
        ((LocalCertification.Information.testingThreshold δ/C)*nearCriticalScale n j ε)
        (Cu*nearCriticalScale n j ε*Real.log (1/δ))
      B l (-η) ∧ B h η ∧ (∀ b ∈ Icc l h, B b 0) := by
  obtain ⟨C, Cu, hC, hCu, G, hG, N, _, hall⟩ :=
    qudit_nearCritical_product_hierarchy_uniform.{u} d j hd l h η hl hlh hh hη hw
  refine ⟨C, Cu, hC, hCu, G, hG, N, ?_⟩
  intro n hn ψ hψ
  exact ⟨hall n hn ψ hψ l le_rfl hlh (-η) le_rfl (by linarith) δ hδ hhalf,
    hall n hn ψ hψ h hlh le_rfl η (by linarith) le_rfl δ hδ hhalf,
    fun b hb => hall n hn ψ hψ b hb.1 hb.2 0 (by linarith) hη.le δ hδ hhalf⟩

example (n j : ℕ) (ε : ℝ) (he : 0 ≤ ε) (hc : (n:ℝ)*ε^2 = 1) :
    nearCriticalScale n j ε = (n:ℝ)^(j+1)/2 := by
  rw [nearCriticalScale, max_eq_left he, hc]
  norm_num

example (n j : ℕ) {ε : ℝ} (h : ε ≤ 0) :
    nearCriticalCostOrder n j ε = (n:ℝ)^(j+1) := by
  simp [nearCriticalCostOrder, not_lt.mpr h]

/-- Uniform comparison of the two optimized costs, in the thresholds and
confidence of the main statement. The bounds use its explicit piecewise rate. -/
example (d j : ℕ) [NeZero d] (hd : 2 ≤ d) (a₀ b₀ : ℝ)
    (hb : 0 < b₀) (hab : b₀ < a₀) (ha : a₀ ≤ 1)
    (hcenter : (a₀-b₀)/(1-b₀) = LocalCertification.Manuscript.gamma d j) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (a₀,b₀) ∈ U ∧
      (∀ x ∈ U, 0 < x.2 ∧ x.2 < x.1 ∧ x.1 ≤ 1) ∧
      ∃ G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (G n))
        atTop (𝓝 1) ∧
      ∃ H : ℝ, 0 < H ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ δstar : ℝ, 0 < δstar → δstar < 1/2 → ∃ L : ℝ, 0 < L ∧
        ∀ (a b δ : ℝ), (a,b) ∈ U → 0 < δ → δ ≤ δstar →
        ∀ n ≥ N, ∀ ψ ∈ G n,
          let ε := (a-b)/(1-b) - LocalCertification.Manuscript.gamma d j
          let R := if 0 < ε then min ((n:ℝ)^j/ε^2) ((n:ℝ)^(j+1)) else (n:ℝ)^(j+1)
          ENNReal.ofReal (L*R*Real.log (1/δ)) ≤
            ProductBudget.expectedBudget.{u} (spherePureVector ψ) a b δ ∧
          ProductBudget.expectedBudget.{u} (spherePureVector ψ) a b δ ≤
            ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ) a b δ) ∧
          ∃ m : ℕ, ProductBudget.capFeasible.{u} (spherePureVector ψ) a b δ m ∧
            (m:ℝ) ≤ H*R*Real.log (1/δ) ∧
            ENat.toENNReal (ProductBudget.maximumBudget.{u} (spherePureVector ψ) a b δ) ≤
              ENNReal.ofReal (H*R*Real.log (1/δ)) := by
  obtain ⟨U, ho, h₀, hv, H, hH, G, hG, N, hN, hconf⟩ :=
    LocalCertification.Paper.corollary_2.{u} d j hd a₀ b₀ hb (lt_of_lt_of_le hab ha) hcenter
  refine ⟨U, ho, h₀, fun x hx => ⟨(hv x hx).1, (hv x hx).2.1, (hv x hx).2.2.le⟩,
    G, hG.2.1, H, hH, N, hN, ?_⟩
  intro δstar hs hh
  obtain ⟨L,hL,hbound⟩ := hconf δstar hs hh
  exact ⟨L,hL, fun a b δ hx hδ hc n hn ψ hψ => hbound n hn ψ hψ (a,b) hx δ hδ hc⟩

example (n : ℕ) (ε : ℝ) (hp : 0 < ε) :
    nearCriticalCostOrder n 0 ε = min (1/ε^2) (n : ℝ) := by
  simp [nearCriticalCostOrder, hp]

end MovingThresholdChecks

#eval IO.println "NearCriticalStatements_PASS"
