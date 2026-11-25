import LocalCertification.Protocol.UniformNearCriticalLower
import LocalCertification.Protocol.NearCriticalProductUpper
import LocalCertification.Protocol.NearCriticalProductAssembly
import LocalCertification.Information.ContinuousConfidenceRatio

/-! Near a critical gap, the same compact Haar-typical family works for
both varying fidelity thresholds. The exact testing factor is available
over the full confidence range, and compactness of the confidence ratio
gives the logarithmic version on each fixed confidence interval. -/

set_option autoImplicit false
open MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum
open LocalCertification.Extremal LocalCertification.Information
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.MeasurableExecution
universe u

/-- The interpolation scale in the supplemental near-critical budget estimate. -/
def nearCriticalScale (n j : ℕ) (ε : ℝ) : ℝ :=
  (n:ℝ)^(j+1)/(1+(n:ℝ)*(max ε 0)^2)

/-- The two optimal budgets, with an actual every-path integer cap witnessing the upper bound. -/
def NearCriticalBudgetBounds {d n : ℕ} [NeZero d] (ψ : QIT.PureVector (QuditIndex d n))
    (a b δ lower upper : ℝ) : Prop :=
  ENNReal.ofReal lower ≤ ProductBudget.expectedBudget.{u} ψ a b δ ∧
  ProductBudget.expectedBudget.{u} ψ a b δ ≤ ENat.toENNReal (ProductBudget.maximumBudget.{u} ψ a b δ) ∧
  ∃ m : ℕ, ProductBudget.capFeasible.{u} ψ a b δ m ∧ (m:ℝ) ≤ upper ∧
    ENat.toENNReal (ProductBudget.maximumBudget.{u} ψ a b δ) ≤ ENNReal.ofReal upper

theorem NearCriticalBudgetBounds.mono {d n : ℕ} [NeZero d] {ψ : QIT.PureVector (QuditIndex d n)}
    {a b δ l l' h h' : ℝ} (hb : NearCriticalBudgetBounds.{u} ψ a b δ l h)
    (hl : l' ≤ l) (hu : h ≤ h') : NearCriticalBudgetBounds.{u} ψ a b δ l' h' := by
  obtain ⟨hlow, hmid, m, hcap, hm, hmax⟩ := hb
  exact ⟨(ENNReal.ofReal_le_ofReal hl).trans hlow, hmid, m, hcap, hm.trans hu,
    hmax.trans (ENNReal.ofReal_le_ofReal hu)⟩

/-- Canonical sphere typicality, including the compact pullback and its exact Haar mass. -/
def CompactHaarTypical (d : ℕ) [NeZero d]
    (G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)) : Prop :=
  (∀ n, IsCompact (G n)) ∧
  Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (G n))
    atTop (nhds 1) ∧
  (∀ n (ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
    IsCompact {U : ComplexUnitary (QuditIndex d n) | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ G n} ∧
    complexUnitaryHaar (QuditIndex d n)
      {U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈ G n} =
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (G n))

/-- SM V.C, the closed near-critical budget estimate. All constants, the
typical targets, and the size cutoff precede both thresholds and confidence. -/
theorem qudit_nearCritical_product_hierarchy_uniform (d j : ℕ) [NeZero d] (hd : 2 ≤ d)
    (bmin bmax η : ℝ) (hmin : 0 < bmin) (hI : bmin ≤ bmax) (hmax : bmax < 1)
    (hη : 0 < η) (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    ∃ C Cupper : ℝ, 0 < C ∧ 0 < Cupper ∧
    ∃ G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
    CompactHaarTypical d G ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n, N ≤ n → ∀ ψ ∈ G n, ∀ b : ℝ, bmin ≤ b → b ≤ bmax →
      ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ < 1/2 →
        NearCriticalBudgetBounds.{u} (spherePureVector ψ)
          (b+(1-b)*(gamma ((d:ℝ)+1) j+ε)) b δ
          ((testingThreshold δ / C) * nearCriticalScale n j ε)
          (Cupper * nearCriticalScale n j ε * Real.log (1/δ)) := by
  obtain ⟨C, hC, hLower⟩ := nearCritical_lower_eventually_uniform.{u} d j hd
    bmin bmax η hmin hI hmax hη hwindow
  let P (n : ℕ) (s : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)) : Prop :=
    canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) sᶜ ≤
      ENNReal.ofReal (measurableNearCriticalFailure d j n) ∧
    ∀ ψ ∈ s, ∀ b : ℝ, bmin ≤ b → b ≤ bmax → ∀ ε : ℝ, -η ≤ ε → ε ≤ η →
    ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ENNReal.ofReal ((testingThreshold δ/C) * nearCriticalScale n j ε) ≤
        ProductBudget.expectedBudget.{u} (spherePureVector ψ) (b+(1-b)*(gamma ((d:ℝ)+1) j+ε)) b δ
  obtain ⟨goodL,hcompactL,hLower⟩ := choose_compact_good P hLower
  have hprobL : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (goodL n))
      atTop (nhds 1) := by
    have hz : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (goodL n)ᶜ)
        atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (measurableNearCriticalFailure_ofReal_tendsto hd j)
        (Filter.Eventually.of_forall (fun _ => bot_le)) (hLower.mono (fun _ h => h.1))
    have h := (ENNReal.continuous_sub_left (show (1 : ℝ≥0∞) ≠ ∞ by simp)).continuousAt.tendsto.comp hz
    have heq (n : ℕ) : 1-canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (goodL n)ᶜ =
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (goodL n) := by
      simpa only [compl_compl] using (prob_compl_eq_one_sub (hcompactL n).isClosed.measurableSet.compl).symm
    simpa only [Function.comp_def, tsub_zero, heq] using h
  obtain ⟨Cupper,hCupper,goodU,hcompactU,hprobU,NU,hNU,hUpper⟩ :=
    qudit_nearCritical_product_upper_uniform.{u} d j hd bmin bmax η hmin hI hmax hη hwindow
  obtain ⟨NL,hLower⟩ := eventually_atTop.mp hLower
  let G := fun n => goodL n ∩ goodU n
  have hc : ∀ n, IsCompact (G n) := fun n => (hcompactL n).inter (hcompactU n)
  have hp : Tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (G n))
      atTop (nhds 1) :=
    probability_inter_tendsto (fun n => canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)))
      goodL goodU (fun n => (hcompactL n).isClosed.measurableSet)
      (fun n => (hcompactU n).isClosed.measurableSet) hprobL hprobU
  refine ⟨C, Cupper, hC, hCupper, G,
    ⟨hc, hp, fun n => compact_good_haar_measure (G n) (hc n)⟩,
    max NL NU, hNU.trans (le_max_right _ _), ?_⟩
  intro n hn ψ hψ b hl hu ε hel heu δ hδ hhalf
  have hL := (hLower n ((le_max_left _ _).trans hn)).2 ψ hψ.1 b hl hu ε hel heu δ hδ hhalf
  obtain ⟨m, hcap, hm, hmid, hmax'⟩ :=
    hUpper n ((le_max_right _ _).trans hn) ψ hψ.2 b hl hu ε hel heu δ hδ hhalf
  exact ⟨hL, hmid, m, hcap, hm, hmax'⟩

/-- Fixed-confidence-range comparison on the same compact two-parameter region.
Only the lower coefficient depends on the chosen confidence cutoff. -/
theorem qudit_nearCritical_product_confidence_uniform (d j : ℕ) [NeZero d] (hd : 2 ≤ d)
    (bmin bmax η : ℝ) (hmin : 0 < bmin) (hI : bmin ≤ bmax) (hmax : bmax < 1)
    (hη : 0 < η) (hwindow : η < (1/2 : ℝ) * min
      ((if j = 0 then 1 else gamma ((d : ℝ)+1) (j-1)) - gamma ((d : ℝ)+1) j)
      (gamma ((d : ℝ)+1) j - gamma ((d : ℝ)+1) (j+1))) :
    ∃ Cupper : ℝ, 0 < Cupper ∧
    ∃ G : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
    CompactHaarTypical d G ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ δstar : ℝ, 0 < δstar → δstar < 1/2 → ∃ c : ℝ, 0 < c ∧
      ∀ n, N ≤ n → ∀ ψ ∈ G n, ∀ b : ℝ, bmin ≤ b → b ≤ bmax →
      ∀ ε : ℝ, -η ≤ ε → ε ≤ η → ∀ δ : ℝ, 0 < δ → δ ≤ δstar →
        NearCriticalBudgetBounds.{u} (spherePureVector ψ)
          (b+(1-b)*(gamma ((d:ℝ)+1) j+ε)) b δ
          (c * nearCriticalScale n j ε * Real.log (1/δ))
          (Cupper * nearCriticalScale n j ε * Real.log (1/δ)) := by
  obtain ⟨C, Cu, hC, hCu, G, hG, N, hN, hall⟩ :=
    qudit_nearCritical_product_hierarchy_uniform.{u} d j hd bmin bmax η hmin hI hmax hη hwindow
  refine ⟨Cu, hCu, G, hG, N, hN, ?_⟩
  intro δstar hs hshalf
  obtain ⟨c, hc, hratio⟩ := testingThreshold_confidence_lower_via_continuous_ratio δstar hs hshalf
  refine ⟨c/C, div_pos hc hC, ?_⟩
  intro n hn ψ hψ b hl hu ε hel heu δ hδ hcut
  apply (hall n hn ψ hψ b hl hu ε hel heu δ hδ (hcut.trans_lt hshalf)).mono _ le_rfl
  have hr := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (hratio δ hδ hcut) hC.le)
    (show 0 ≤ nearCriticalScale n j ε by unfold nearCriticalScale; positivity)
  convert hr using 1
  ring

end LocalCertification.Protocol.MeasurableExecution

