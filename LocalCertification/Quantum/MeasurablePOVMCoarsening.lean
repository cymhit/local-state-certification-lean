import LocalCertification.Quantum.MeasurablePOVMRankOne
import LocalCertification.Information.DensityCoarsening

/-!
# Born reference densities and genuine POVM coarse-graining

The original trace-reference density is bounded by the Hilbert-space dimension.
For the measurable rank-one refinement, forgetting its auxiliary index pushes
forward both the reference probability and every state's actual Born law.
These proved identities instantiate reference L2 and relative-entropy
contractions, preserving the original outcome labels and the ordered state pair.
-/

set_option autoImplicit false
open MeasureTheory Matrix InformationTheory
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.Elementwise
noncomputable section

namespace LocalCertification.Quantum.MeasurablePOVM

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Nonempty I]

local instance coarseningMatrixContinuousENorm : ContinuousENorm (Matrix I I ℂ) := SeminormedAddGroup.toContinuousENorm

/-- Born density with respect to the actual normalized trace probability. -/
def bornDensity (M : MeasurablePOVM Ω I) (ρ : QIT.State I) (s : Ω) : ℝ :=
  (ρ.matrix * M.traceDensity s).trace.re

private def bornTraceMap (ρ : QIT.State I) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (ρ.matrix * A).trace.re
  map_add' _ _ := by simp [Matrix.mul_add]
  map_smul' _ _ := by simp
  cont := by fun_prop

theorem bornDensity_measurable (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    Measurable (M.bornDensity ρ) :=
  (bornTraceMap ρ).continuous.measurable.comp M.traceDensity_measurable

theorem bornDensity_integrable (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    Integrable (M.bornDensity ρ) M.traceReference :=
  (bornTraceMap ρ).integrable_comp M.traceDensity_integrable

theorem bornDensity_nonneg (M : MeasurablePOVM Ω I) (ρ : QIT.State I) (s : Ω) :
    0 ≤ M.bornDensity ρ s :=
  QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten ρ.pos (M.traceDensity_pos s)

theorem bornDensity_le (M : MeasurablePOVM Ω I) (ρ : QIT.State I) (s : Ω) :
    M.bornDensity ρ s ≤ (Fintype.card I : ℝ) := by
  have hρ : ρ.matrix ≤ 1 := by
    apply QIT.posSemidef_le_one_of_psdTracePower_le_one ρ.pos (q := 1) zero_lt_one
    rw [QIT.psdTracePower_one, ρ.trace_eq_one]
    norm_num
  have ht := QIT.cMatrix_trace_mul_le_of_le_posSemidef_right (M.traceDensity_pos s) hρ
  simpa only [bornDensity, Matrix.one_mul, M.traceDensity_trace, Complex.natCast_re] using ht

theorem integral_bornDensity (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    ∫ s, M.bornDensity ρ s ∂M.traceReference = 1 := by
  have hm : (∫ s, M.traceDensity s ∂M.traceReference) = 1 := by
    simpa only [Measure.restrict_univ, M.univ] using M.traceDensity_setIntegral MeasurableSet.univ
  change (∫ s, bornTraceMap ρ (M.traceDensity s) ∂M.traceReference) = 1
  refine ((bornTraceMap ρ).integral_comp_comm M.traceDensity_integrable).trans ?_
  refine (congrArg (fun B => bornTraceMap ρ B) hm).trans ?_
  simp [bornTraceMap, ρ.trace_eq_one]

theorem born_eq_withDensity (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    M.born ρ = M.traceReference.withDensity (fun s => ENNReal.ofReal (M.bornDensity ρ s)) :=
  M.born_eq_withDensity_traceDensity ρ

theorem bornDensity_maximallyMixed (M : MeasurablePOVM Ω I) (s : Ω) :
    M.bornDensity (QIT.State.maximallyMixed I) s = 1 := by
  simp [bornDensity, QIT.State.maximallyMixed_matrix, Matrix.trace_smul,
    M.traceDensity_trace, Fintype.card_ne_zero]

variable [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The original squared density difference is no greater than its genuine
rank-one refinement, with the same reference and the same ordered state pair. -/
theorem referenceL2_sq_le_refinement (M : MeasurablePOVM Ω I) (ρ σ : QIT.State I) :
    (∫ s, (M.bornDensity ρ s - M.bornDensity σ s)^2 ∂M.traceReference) ≤
      ∫ p, (M.refinedBornDensity ρ p - M.refinedBornDensity σ p)^2 ∂M.refinementReference := by
  have hpush (τ : QIT.State I) :
      (M.refinementReference.withDensity (fun p => ENNReal.ofReal (M.refinedBornDensity τ p))).map
        Prod.fst = M.traceReference.withDensity (fun s => ENNReal.ofReal (M.bornDensity τ s)) := by
    rw [← M.born_eq_withDensity τ, ← M.refinedPOVM_born_map_fst τ]
    congr 1
    exact (M.refinedPOVM_born_eq_withDensity τ).symm
  exact Information.DensityCoarsening.integral_difference_sq_le
    M.refinementReference M.traceReference Prod.fst measurable_fst M.refinementReference_map_fst
    (M.refinedBornDensity ρ) (M.refinedBornDensity σ) (M.bornDensity ρ) (M.bornDensity σ)
    (M.refinedBornDensity_measurable ρ) (M.refinedBornDensity_measurable σ)
    (M.bornDensity_measurable ρ) (M.bornDensity_measurable σ) (Fintype.card I) (Nat.cast_nonneg _)
    (fun p => ⟨M.refinedBornDensity_nonneg ρ p, M.refinedBornDensity_le ρ p⟩)
    (fun p => ⟨M.refinedBornDensity_nonneg σ p, M.refinedBornDensity_le σ p⟩)
    (fun s => ⟨M.bornDensity_nonneg ρ s, M.bornDensity_le ρ s⟩)
    (fun s => ⟨M.bornDensity_nonneg σ s, M.bornDensity_le σ s⟩) (hpush ρ) (hpush σ)

/-- Coarse-graining the actual Born laws contracts KL in the same order. -/
theorem born_klDiv_le_refinement (M : MeasurablePOVM Ω I) (ρ σ : QIT.State I) :
    klDiv (M.born ρ) (M.born σ) ≤ klDiv (M.refinedPOVM.born ρ) (M.refinedPOVM.born σ) := by
  rw [← M.refinedPOVM_born_map_fst ρ, ← M.refinedPOVM_born_map_fst σ]
  exact Information.DensityCoarsening.klDiv_coarsen_le
    (M.refinedPOVM.born ρ) (M.refinedPOVM.born σ) Prod.fst measurable_fst

end LocalCertification.Quantum.MeasurablePOVM
