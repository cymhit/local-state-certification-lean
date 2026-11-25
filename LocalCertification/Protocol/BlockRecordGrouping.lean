import LocalCertification.Protocol.FixedBornProtocol
import LocalCertification.Probability.BlockAmplification

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical Set LocalCertification.Probability
open scoped BigOperators ENNReal
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A bijective measurable regrouping of the actual flat sequence into consecutive finite blocks. -/
def blockRecordGrouping (m k : ℕ) : (Fin (k*m) → Ω) ≃ᵐ (Fin k → Fin m → Ω) where
  toFun x i j := x (finProdFinEquiv (i,j))
  invFun y i := y (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  left_inv x := by
    funext i
    change x (finProdFinEquiv (finProdFinEquiv.symm i)) = x i
    rw [Equiv.apply_symm_apply]
  right_inv y := by
    funext i j
    change y (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = y i j
    rw [Equiv.symm_apply_apply]
  measurable_toFun := measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j =>
    measurable_pi_apply (finProdFinEquiv (i,j))))
  measurable_invFun := measurable_pi_iff.mpr (fun i =>
    (measurable_pi_apply (finProdFinEquiv.symm i).2).comp (measurable_pi_apply (finProdFinEquiv.symm i).1))

/-- The exact flat iid law is the actual two-level iid block law after regrouping, including empty index types. -/
theorem blockRecordGrouping_law (μ : Measure Ω) [IsProbabilityMeasure μ] (m k : ℕ) :
    (Measure.pi (fun _ : Fin (k*m) => μ)).map (blockRecordGrouping m k) =
      Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin m => μ)) := by
  have hr : (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin m => μ))).map
      (blockRecordGrouping m k).symm = Measure.pi (fun _ : Fin (k*m) => μ) := by
    apply Eq.symm
    apply Measure.pi_eq
    intro s hs
    rw [MeasurableEquiv.map_apply]
    have he : (blockRecordGrouping m k).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i : Fin k => Set.univ.pi (fun j : Fin m => s (finProdFinEquiv (i,j)))) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro h i j
        have ht := h (finProdFinEquiv (i,j))
        change y (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
          (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 ∈ s (finProdFinEquiv (i,j)) at ht
        rw [Equiv.symm_apply_apply] at ht
        exact ht
      · intro h i
        have ht := h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
        change y (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 ∈ s (finProdFinEquiv (finProdFinEquiv.symm i)) at ht
        rw [Equiv.apply_symm_apply] at ht
        exact ht
    rw [he, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    calc
      _ = ∏ ij : Fin k × Fin m, μ (s (finProdFinEquiv ij)) :=
        (Fintype.prod_prod_type (fun ij : Fin k × Fin m => μ (s (finProdFinEquiv ij)))).symm
      _ = _ := Fintype.prod_equiv finProdFinEquiv _ _ (fun _ => rfl)
  rw [← hr, Measure.map_map (blockRecordGrouping m k).measurable (blockRecordGrouping m k).symm.measurable]
  simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply, Measure.map_id']

/-- The original protocol convention accepts high with 0, so the probability test's 1-high label is explicitly reversed. -/
def rawMajorityDecision (f : Ω → ℝ) (t : ℝ) (m k : ℕ) (x : Fin (k*m) → Ω) : Fin 2 :=
  Fin.rev (scoreMajorityTest f t m k (blockRecordGrouping m k x))

theorem rawMajorityDecision_measurable (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) (m k : ℕ) :
    Measurable (rawMajorityDecision f t m k) :=
  (measurable_of_countable Fin.rev).comp
    ((scoreMajorityTest_measurable f hf t m k).comp (blockRecordGrouping m k).measurable)

/-- Error labels are translated literally; the high class is rejected exactly when the probability test is not 1. -/
theorem rawMajorityDecision_high_iff (f : Ω → ℝ) (t : ℝ) (m k : ℕ) (x : Fin (k*m) → Ω) :
    rawMajorityDecision f t m k x = 1 ↔ scoreMajorityTest f t m k (blockRecordGrouping m k x) ≠ 1 := by
  unfold rawMajorityDecision
  generalize scoreMajorityTest f t m k (blockRecordGrouping m k x) = j
  fin_cases j <;> decide

theorem rawMajorityDecision_low_iff (f : Ω → ℝ) (t : ℝ) (m k : ℕ) (x : Fin (k*m) → Ω) :
    rawMajorityDecision f t m k x = 0 ↔ scoreMajorityTest f t m k (blockRecordGrouping m k x) ≠ 0 := by
  unfold rawMajorityDecision
  generalize scoreMajorityTest f t m k (blockRecordGrouping m k x) = j
  fin_cases j <;> decide

theorem rawMajorityDecision_error_high (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hfm : Measurable f) (hf : MemLp f 2 μ) {V Δ t δ : ℝ}
    (hV : 0<V) (hΔ : 0<Δ) (hδ : 0<δ) (hδ1 : δ<1)
    (hv : variance f μ≤V) (hmean : t+Δ/4≤∫ y,f y∂μ) :
    Measure.pi (fun _ : Fin (blockCount δ * blockCopies V Δ) => μ)
      {x | rawMajorityDecision f t (blockCopies V Δ) (blockCount δ) x=1} ≤ ENNReal.ofReal δ := by
  have h := scoreMajority_error_high μ f hfm hf hV hΔ hδ hδ1 hv hmean
  rw [← blockRecordGrouping_law μ (blockCopies V Δ) (blockCount δ)] at h
  erw [Measure.map_apply (blockRecordGrouping (blockCopies V Δ) (blockCount δ)).measurable
    (show MeasurableSet {x | scoreMajorityTest f t (blockCopies V Δ) (blockCount δ) x ≠ 1} from
      (measurableSet_eq_fun (scoreMajorityTest_measurable f hfm t _ _) measurable_const).compl)] at h
  convert h using 1
  congr 1
  ext x
  exact rawMajorityDecision_high_iff _ _ _ _ x

theorem rawMajorityDecision_error_low (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hfm : Measurable f) (hf : MemLp f 2 μ) {V Δ t δ : ℝ}
    (hV : 0<V) (hΔ : 0<Δ) (hδ : 0<δ) (hδ1 : δ<1)
    (hv : variance f μ≤V) (hmean : (∫ y,f y∂μ)+Δ/4≤t) :
    Measure.pi (fun _ : Fin (blockCount δ * blockCopies V Δ) => μ)
      {x | rawMajorityDecision f t (blockCopies V Δ) (blockCount δ) x=0} ≤ ENNReal.ofReal δ := by
  have h := scoreMajority_error_low μ f hfm hf hV hΔ hδ hδ1 hv hmean
  rw [← blockRecordGrouping_law μ (blockCopies V Δ) (blockCount δ)] at h
  erw [Measure.map_apply (blockRecordGrouping (blockCopies V Δ) (blockCount δ)).measurable
    (show MeasurableSet {x | scoreMajorityTest f t (blockCopies V Δ) (blockCount δ) x ≠ 0} from
      (measurableSet_eq_fun (scoreMajorityTest_measurable f hfm t _ _) measurable_const).compl)] at h
  convert h using 1
  congr 1
  ext x
  exact rawMajorityDecision_low_iff _ _ _ _ x

end LocalCertification.Protocol
