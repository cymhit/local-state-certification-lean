import LocalCertification.Quantum.MeasurableSpectralBasis
import LocalCertification.Quantum.Boundary
import LocalCertification.Quantum.MeasurablePOVMDensity
import QIT.Core.Pure
import QIT.States.MaximallyMixed
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Measurable rank-one decomposition of a POVM density

The refined labels consist of the original outcome and the index of a
measurable eigenvector. Ordered eigenvalues supply the trace weights.
An auxiliary square-root column decomposition gives another rank-one expansion.
-/

set_option autoImplicit false
open MeasureTheory Matrix
open ProbabilityTheory
open scoped ENNReal ComplexOrder MatrixOrder
noncomputable section

namespace LocalCertification.Quantum.MeasurablePOVM
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Nonempty I]

open scoped Matrix.Norms.L2Operator in
private theorem sqrtDensity_measurable (M : MeasurablePOVM Ω I) :
    Measurable (fun s => QIT.psdSqrt (M.traceDensity s)) :=
  CFC.measurable_sqrt.comp M.traceDensity_measurable

/-- The column rank-one terms of the positive square root of the genuine matrix density. -/
def squareRootColumnEffect (M : MeasurablePOVM Ω I) (s : Ω) (i : I) : Matrix I I ℂ :=
  QIT.rankOneMatrix (fun j => QIT.psdSqrt (M.traceDensity s) j i)

theorem squareRootColumnEffect_measurable (M : MeasurablePOVM Ω I) (i : I) :
    Measurable (fun s => M.squareRootColumnEffect s i) := by
  apply Measurable.of_eval_matrix
  intro j k
  exact ((sqrtDensity_measurable M).eval_matrix (i := j) (j := i)).mul
    (continuous_star.measurable.comp
      ((sqrtDensity_measurable M).eval_matrix (i := k) (j := i)))

theorem squareRootColumnEffect_pos (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    (M.squareRootColumnEffect s i).PosSemidef := QIT.rankOneMatrix_pos _

theorem squareRootColumnEffect_rank (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    (M.squareRootColumnEffect s i).rank ≤ 1 := QIT.rankOneMatrix_rank_le_one _

theorem sum_squareRootColumnEffect (M : MeasurablePOVM Ω I) (s : Ω) :
    ∑ i, M.squareRootColumnEffect s i = M.traceDensity s := by
  calc
    ∑ i, M.squareRootColumnEffect s i = QIT.psdSqrt (M.traceDensity s) *
        (QIT.psdSqrt (M.traceDensity s)).conjTranspose := by
      ext j k
      simp only [Matrix.sum_apply, squareRootColumnEffect, QIT.rankOneMatrix_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = M.traceDensity s := by
      rw [(QIT.psdSqrt_isHermitian _).eq,
        QIT.psdSqrt_mul_self_of_posSemidef (M.traceDensity_pos s)]

/-- The chosen unit eigenvector of the trace-reference density. The fixed
enumeration transfers its ordered finite spectral index to the outcome label. -/
def refinementUnitVector (M : MeasurablePOVM Ω I) (s : Ω) (i : I) : EuclideanSpace ℂ I :=
  measurableSpectralBasis (M.traceDensity_pos s).isHermitian (Fintype.equivFin I i)

theorem refinementUnitVector_measurable_column (M : MeasurablePOVM Ω I) (i : I) :
    Measurable (fun s => M.refinementUnitVector s i) :=
  measurable_spectralBasis M.traceDensity M.traceDensity_measurable
    (fun s => (M.traceDensity_pos s).isHermitian) (Fintype.equivFin I i)

theorem refinementUnitVector_norm (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    ‖M.refinementUnitVector s i‖ = 1 :=
  (measurableSpectralBasis (M.traceDensity_pos s).isHermitian).orthonormal.1 _

/-- Eigenvalue weight, including zero eigenvalues with their multiplicities. -/
def refinementWeight (M : MeasurablePOVM Ω I) (s : Ω) (i : I) : ℝ :=
  selectedEigenvalue (M.traceDensity_pos s).isHermitian (Fintype.equivFin I i)

theorem refinementWeight_nonneg (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    0 ≤ M.refinementWeight s i := selectedEigenvalue_nonneg (M.traceDensity_pos s) _

theorem refinementWeight_measurable (M : MeasurablePOVM Ω I) (i : I) :
    Measurable (fun s => M.refinementWeight s i) :=
  measurable_selectedEigenvalue M.traceDensity M.traceDensity_measurable
    (fun s => (M.traceDensity_pos s).isHermitian) _

/-- The normalized spectral projector is defined even when its reference
weight is zero. -/
def refinementProjector (M : MeasurablePOVM Ω I) (s : Ω) (i : I) : Matrix I I ℂ :=
  QIT.rankOneMatrix (M.refinementUnitVector s i)

theorem refinementProjector_measurable (M : MeasurablePOVM Ω I) (i : I) :
    Measurable (fun s => M.refinementProjector s i) := by
  have hm (j : I) : Measurable (fun s => M.refinementUnitVector s i j) :=
    (PiLp.continuous_apply 2 _ j).measurable.comp (M.refinementUnitVector_measurable_column i)
  apply Measurable.of_eval_matrix
  intro j k
  exact (hm j).mul (continuous_star.measurable.comp (hm k))

theorem refinementProjector_pos (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    (M.refinementProjector s i).PosSemidef := QIT.rankOneMatrix_pos _

theorem refinementProjector_rank (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    (M.refinementProjector s i).rank ≤ 1 := QIT.rankOneMatrix_rank_le_one _

theorem refinementProjector_trace (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    (M.refinementProjector s i).trace = 1 := by
  rw [refinementProjector, rankOne_trace_norm_sq]
  change (‖M.refinementUnitVector s i‖ ^ 2 : ℂ) = 1
  rw [M.refinementUnitVector_norm]
  norm_num

theorem refinementProjector_eq_pure (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    ∃ ψ : QIT.PureVector I, ψ.state.matrix = M.refinementProjector s i :=
  ⟨⟨M.refinementUnitVector s i, M.refinementProjector_trace s i⟩, rfl⟩

/-- The rank-one effects in the spectral decomposition of the density. -/
def refinementEffect (M : MeasurablePOVM Ω I) (s : Ω) (i : I) : Matrix I I ℂ :=
  M.refinementWeight s i • M.refinementProjector s i

theorem weight_smul_refinementProjector (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    M.refinementWeight s i • M.refinementProjector s i = M.refinementEffect s i := rfl

theorem refinementEffect_measurable (M : MeasurablePOVM Ω I) (i : I) :
    Measurable (fun s => M.refinementEffect s i) :=
  (M.refinementWeight_measurable i).smul (M.refinementProjector_measurable i)

theorem refinementEffect_pos (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    (M.refinementEffect s i).PosSemidef :=
  (M.refinementProjector_pos s i).smul (M.refinementWeight_nonneg s i)

theorem refinementEffect_rank (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    (M.refinementEffect s i).rank ≤ 1 := by
  have h := Matrix.rank_mul_le_right ((M.refinementWeight s i) • (1 : Matrix I I ℂ))
    (M.refinementProjector s i)
  simpa only [Matrix.smul_mul, Matrix.one_mul, refinementEffect] using h.trans (M.refinementProjector_rank s i)

theorem sum_refinementEffect (M : MeasurablePOVM Ω I) (s : Ω) :
    ∑ i, M.refinementEffect s i = M.traceDensity s := by
  let F (i : Fin (Fintype.card I)) := selectedEigenvalue (M.traceDensity_pos s).isHermitian i •
    QIT.rankOneMatrix (fun j => measurableSpectralBasis (M.traceDensity_pos s).isHermitian i j)
  exact ((Fintype.equivFin I).sum_comp F).trans
    (sum_selectedEigenvalue_rankOne (M.traceDensity_pos s).isHermitian)

theorem sum_refinementWeight (M : MeasurablePOVM Ω I) (s : Ω) :
    ∑ i, M.refinementWeight s i = (Fintype.card I : ℝ) := by
  have h := congrArg (fun A : Matrix I I ℂ => A.trace.re) (M.sum_refinementEffect s)
  simpa only [Matrix.trace_sum, Complex.re_sum, refinementEffect, Matrix.trace_smul,
    refinementProjector_trace, Complex.smul_re, smul_eq_mul, Complex.one_re, mul_one,
    M.traceDensity_trace, Complex.natCast_re] using h

theorem refinementProjector_mul_self (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    M.refinementProjector s i * M.refinementProjector s i = M.refinementProjector s i := by
  obtain ⟨ψ, hψ⟩ := M.refinementProjector_eq_pure s i
  rw [← hψ]
  exact ψ.state_matrix_mul_self

private def refinementPMF (M : MeasurablePOVM Ω I) (s : Ω) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (M.refinementWeight s i / Fintype.card I)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      div_nonneg (M.refinementWeight_nonneg s i) (Nat.cast_nonneg _)),
      ← Finset.sum_div, M.sum_refinementWeight]
    simp [Fintype.card_ne_zero])

section RefinementMeasure
variable [MeasurableSpace I] [MeasurableSingletonClass I]

section L2Helpers
open scoped Matrix.Norms.L2Operator
local instance : ContinuousENorm (Matrix I I ℂ) := SeminormedAddGroup.toContinuousENorm

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
private theorem refinementProjector_norm_le (M : MeasurablePOVM Ω I) (s : Ω) (i : I) :
    ‖M.refinementProjector s i‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (M.refinementProjector_pos s i).nonneg).mpr
  apply QIT.posSemidef_le_one_of_psdTracePower_le_one
    (M.refinementProjector_pos s i) (q := 1) zero_lt_one
  rw [QIT.psdTracePower_one, M.refinementProjector_trace]
  norm_num

private def matrixToPi : Matrix I I ℂ →L[ℝ] (I → I → ℂ) where
  toFun A := A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_id

private theorem refinementProjector_pi_integrable (M : MeasurablePOVM Ω I)
    (ν : Measure (Ω × I)) [IsFiniteMeasure ν] :
    Integrable (fun p => matrixToPi (M.refinementProjector p.1 p.2)) ν := by
  have hm : Measurable (fun p : Ω × I => M.refinementProjector p.1 p.2) :=
    measurable_from_prod_countable_left (M.refinementProjector_measurable)
  have hi : Integrable (fun p : Ω × I => M.refinementProjector p.1 p.2) ν :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => refinementProjector_norm_le M p.1 p.2))
  exact matrixToPi.integrable_comp hi

end L2Helpers

/-- The finite auxiliary column-index kernel, conditional on the original outcome. -/
def refinementKernel (M : MeasurablePOVM Ω I) : Kernel Ω I where
  toFun s := (refinementPMF M s).toMeasure
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [refinementPMF, PMF.toMeasure_ofFintype_apply _ _ hA, tsum_fintype]
    apply Finset.measurable_sum
    intro i _
    by_cases hi : i ∈ A
    · simp only [Set.indicator_of_mem hi]
      exact ((M.refinementWeight_measurable i).div_const _).ennreal_ofReal
    · simp only [Set.indicator_of_notMem hi]
      exact measurable_const

instance refinementKernel_markov (M : MeasurablePOVM Ω I) : IsMarkovKernel M.refinementKernel where
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

/-- Reference probability on the original outcome together with the refinement index. -/
def refinementReference (M : MeasurablePOVM Ω I) : Measure (Ω × I) :=
  M.traceReference ⊗ₘ M.refinementKernel

instance refinementReference_probability (M : MeasurablePOVM Ω I) :
    IsProbabilityMeasure M.refinementReference := by
  unfold refinementReference
  infer_instance

omit [MeasurableSingletonClass I] in
theorem refinementReference_map_fst (M : MeasurablePOVM Ω I) :
    M.refinementReference.map Prod.fst = M.traceReference :=
  Measure.fst_compProd _ _

open scoped Matrix.Norms.Elementwise in
theorem integral_refinementKernel (M : MeasurablePOVM Ω I) (s : Ω) :
    ∫ i, (Fintype.card I : ℝ) • M.refinementProjector s i ∂M.refinementKernel s =
      M.traceDensity s := by
  change ∫ i, (Fintype.card I : ℝ) • M.refinementProjector s i ∂(refinementPMF M s).toMeasure = _
  rw [integral_fintype .of_finite]
  have hd : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    refinementPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (div_nonneg (M.refinementWeight_nonneg s _) (Nat.cast_nonneg _)),
    smul_smul, div_mul_cancel₀ _ hd,
    M.weight_smul_refinementProjector]
  exact M.sum_refinementEffect s

open scoped Matrix.Norms.Elementwise

local instance : ContinuousENorm (Matrix I I ℂ) := SeminormedAddGroup.toContinuousENorm

private def adjointIntegralMap : Matrix I I ℂ →L[ℝ] Matrix I I ℂ where
  toFun A := A.conjTranspose
  map_add' A B := Matrix.conjTranspose_add A B
  map_smul' _ _ := by simp
  cont := by fun_prop

private def quadraticIntegralMap (v : I → ℂ) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (star v ⬝ᵥ (A *ᵥ v)).re
  map_add' _ _ := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' _ _ := by simp [Matrix.smul_mulVec, dotProduct_smul]
  cont := by unfold Matrix.mulVec dotProduct; fun_prop

omit [DecidableEq I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I] in
private theorem integral_posSemidef {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {f : X → Matrix I I ℂ} (hf : Integrable f ν) (hp : ∀ x, (f x).PosSemidef) :
    (∫ x, f x ∂ν).PosSemidef := by
  have hH : (∫ x, f x ∂ν).IsHermitian := by
    exact (adjointIntegralMap.integral_comp_comm hf).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall (fun x => (hp x).isHermitian.eq)))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  constructor
  · have h : 0 ≤ ∫ x, quadraticIntegralMap v (f x) ∂ν :=
      integral_nonneg (fun x => (hp x).re_dotProduct_nonneg v)
    change 0 ≤ quadraticIntegralMap v (∫ x, f x ∂ν)
    exact ((quadraticIntegralMap v).integral_comp_comm hf) ▸ h
  · exact (hH.im_star_dotProduct_mulVec_self v).symm

/-- The trace-normalized refined matrix density, on the original outcome and finite index. -/
def refinementDensity (M : MeasurablePOVM Ω I) (p : Ω × I) : Matrix I I ℂ :=
  (Fintype.card I : ℝ) • M.refinementProjector p.1 p.2

theorem refinementDensity_measurable (M : MeasurablePOVM Ω I) :
    Measurable M.refinementDensity := by
  have h : Measurable (fun p : Ω × I => M.refinementProjector p.1 p.2) :=
    measurable_from_prod_countable_left M.refinementProjector_measurable
  exact (measurable_const : Measurable (fun _ : Ω × I => (Fintype.card I : ℝ))).smul h

theorem refinementDensity_integrable (M : MeasurablePOVM Ω I) :
    Integrable M.refinementDensity M.refinementReference := by
  have hi : Integrable (fun p : Ω × I => M.refinementProjector p.1 p.2) M.refinementReference :=
    refinementProjector_pi_integrable M _
  exact hi.smul (Fintype.card I : ℝ)

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
theorem refinementDensity_pos (M : MeasurablePOVM Ω I) (p : Ω × I) :
    (M.refinementDensity p).PosSemidef :=
  (M.refinementProjector_pos p.1 p.2).smul (Nat.cast_nonneg _)

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
theorem refinementDensity_trace (M : MeasurablePOVM Ω I) (p : Ω × I) :
    (M.refinementDensity p).trace = (Fintype.card I : ℂ) := by
  simp [refinementDensity, Matrix.trace_smul, M.refinementProjector_trace]

private theorem integral_refinementDensity (M : MeasurablePOVM Ω I) :
    ∫ p, M.refinementDensity p ∂M.refinementReference = 1 := by
  change ∫ p, M.refinementDensity p ∂(M.traceReference ⊗ₘ M.refinementKernel) = _
  rw [Measure.integral_compProd M.refinementDensity_integrable]
  have h := M.traceDensity_setIntegral MeasurableSet.univ
  simpa only [refinementDensity, M.integral_refinementKernel, Measure.restrict_univ, M.univ] using h

/-- The actual rank-one refinement POVM. Original outcomes are retained as the first label. -/
def refinedPOVM (M : MeasurablePOVM Ω I) : MeasurablePOVM (Ω × I) I where
  toVectorMeasure := M.refinementReference.withDensityᵥ M.refinementDensity
  positive A hA := by
    have h : (∫ p in A, M.refinementDensity p ∂M.refinementReference).PosSemidef :=
      integral_posSemidef _ M.refinementDensity_integrable.integrableOn M.refinementDensity_pos
    exact (withDensityᵥ_apply M.refinementDensity_integrable hA).symm ▸ h
  univ := by
    exact (withDensityᵥ_apply M.refinementDensity_integrable MeasurableSet.univ).trans
      (by simpa only [Measure.restrict_univ] using integral_refinementDensity M)

theorem refinedPOVM_apply (M : MeasurablePOVM Ω I) {A : Set (Ω × I)} (hA : MeasurableSet A) :
    M.refinedPOVM.toVectorMeasure A = ∫ p in A, M.refinementDensity p ∂M.refinementReference :=
  withDensityᵥ_apply M.refinementDensity_integrable hA

/-- Forgetting the auxiliary index recovers the original matrix effect of every measurable event. -/
theorem refinedPOVM_apply_preimage_fst (M : MeasurablePOVM Ω I) {A : Set Ω}
    (hA : MeasurableSet A) :
    M.refinedPOVM.toVectorMeasure (Prod.fst ⁻¹' A) = M.toVectorMeasure A := by
  refine (M.refinedPOVM_apply (hA.preimage measurable_fst)).trans ?_
  have hprod : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set I) := by ext p; simp
  rw [hprod]
  have h := Measure.setIntegral_compProd (μ := M.traceReference) (κ := M.refinementKernel)
    hA MeasurableSet.univ M.refinementDensity_integrable.integrableOn
  change (∫ p in A ×ˢ Set.univ, M.refinementDensity p
    ∂(M.traceReference ⊗ₘ M.refinementKernel)) = _
  refine h.trans ?_
  simpa only [refinementDensity, Measure.restrict_univ, M.integral_refinementKernel] using
    M.traceDensity_setIntegral hA

/-- The original outcome record has exactly its original Born distribution after refinement. -/
theorem refinedPOVM_born_map_fst (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    (M.refinedPOVM.born ρ).map Prod.fst = M.born ρ := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_fst hA, M.refinedPOVM.born_apply ρ (hA.preimage measurable_fst),
    M.refinedPOVM_apply_preimage_fst hA, M.born_apply ρ hA]

private def normalizedTraceMap : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := A.trace.re / Fintype.card I
  map_add' _ _ := by simp [add_div]
  map_smul' _ _ := by simp [mul_div_assoc]
  cont := by fun_prop

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
private theorem normalizedTrace_refinementDensity (M : MeasurablePOVM Ω I) (p : Ω × I) :
    normalizedTraceMap (M.refinementDensity p) = 1 := by
  change (M.refinementDensity p).trace.re / Fintype.card I = 1
  simp [M.refinementDensity_trace, Fintype.card_ne_zero]

/-- The refined reference is the normalized trace measure of the actual refined POVM. -/
theorem refinedPOVM_traceReference (M : MeasurablePOVM Ω I) :
    M.refinedPOVM.traceReference = M.refinementReference := by
  apply Measure.ext
  intro A hA
  rw [M.refinedPOVM.traceReference_apply hA]
  have h : normalizedTraceMap (M.refinedPOVM.toVectorMeasure A) = M.refinementReference.real A := by
    refine (congrArg (fun B => normalizedTraceMap B) (M.refinedPOVM_apply hA)).trans ?_
    refine (normalizedTraceMap.integral_comp_comm
      (μ := M.refinementReference.restrict A) M.refinementDensity_integrable.integrableOn).symm.trans ?_
    refine (integral_congr_ae (Filter.Eventually.of_forall
      (fun p => normalizedTrace_refinementDensity M p))).trans ?_
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ]
  change ENNReal.ofReal (normalizedTraceMap (M.refinedPOVM.toVectorMeasure A)) = _
  rw [h, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

private def refinementStateMap (ρ : QIT.State I) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (ρ.matrix * A).trace.re
  map_add' _ _ := by simp [Matrix.mul_add]
  map_smul' _ _ := by simp
  cont := by fun_prop

/-- Explicit rank-one Born density with respect to the same refined reference probability. -/
theorem refinedPOVM_born_eq_withDensity (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    M.refinedPOVM.born ρ = M.refinementReference.withDensity
      (fun p => ENNReal.ofReal ((Fintype.card I : ℝ) *
        (ρ.matrix * M.refinementProjector p.1 p.2).trace.re)) := by
  apply Measure.ext
  intro A hA
  rw [M.refinedPOVM.born_apply ρ hA, withDensity_apply _ hA]
  have hi := (refinementStateMap ρ).integrable_comp M.refinementDensity_integrable
  have hn : ∀ p, 0 ≤ refinementStateMap ρ (M.refinementDensity p) := fun p =>
    QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten ρ.pos (M.refinementDensity_pos p)
  have h := ofReal_integral_eq_lintegral_ofReal (μ := M.refinementReference.restrict A)
    hi.integrableOn (Filter.Eventually.of_forall hn)
  have heq : (∫ p in A, refinementStateMap ρ (M.refinementDensity p) ∂M.refinementReference) =
      refinementStateMap ρ (M.refinedPOVM.toVectorMeasure A) :=
    ((refinementStateMap ρ).integral_comp_comm
      (μ := M.refinementReference.restrict A) M.refinementDensity_integrable.integrableOn).trans
      (congrArg (fun B => refinementStateMap ρ B) (M.refinedPOVM_apply hA).symm)
  have hfinal := (congrArg ENNReal.ofReal heq).symm.trans h
  refine hfinal.trans (lintegral_congr (fun p => ?_))
  congr 1
  change (ρ.matrix * ((Fintype.card I : ℝ) • M.refinementProjector p.1 p.2)).trace.re = _
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- The real Born density in the normalized rank-one representation. -/
def refinedBornDensity (M : MeasurablePOVM Ω I) (ρ : QIT.State I) (p : Ω × I) : ℝ :=
  (Fintype.card I : ℝ) * (ρ.matrix * M.refinementProjector p.1 p.2).trace.re

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
private theorem refinedBornDensity_eq (M : MeasurablePOVM Ω I) (ρ : QIT.State I) (p : Ω × I) :
    M.refinedBornDensity ρ p = refinementStateMap ρ (M.refinementDensity p) := by
  change (Fintype.card I : ℝ) * (ρ.matrix * M.refinementProjector p.1 p.2).trace.re =
    (ρ.matrix * ((Fintype.card I : ℝ) • M.refinementProjector p.1 p.2)).trace.re
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem refinedBornDensity_measurable (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    Measurable (M.refinedBornDensity ρ) := by
  have h := (refinementStateMap ρ).continuous.measurable.comp M.refinementDensity_measurable
  have he : M.refinedBornDensity ρ = (refinementStateMap ρ) ∘ M.refinementDensity :=
    funext (refinedBornDensity_eq M ρ)
  exact he ▸ h

theorem refinedBornDensity_integrable (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    Integrable (M.refinedBornDensity ρ) M.refinementReference :=
  ((refinementStateMap ρ).integrable_comp M.refinementDensity_integrable).congr
    (Filter.Eventually.of_forall (fun p => (refinedBornDensity_eq M ρ p).symm))

theorem integral_refinedBornDensity (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    ∫ p, M.refinedBornDensity ρ p ∂M.refinementReference = 1 := by
  refine (integral_congr_ae (Filter.Eventually.of_forall (refinedBornDensity_eq M ρ))).trans ?_
  refine ((refinementStateMap ρ).integral_comp_comm M.refinementDensity_integrable).trans ?_
  refine (congrArg (fun B => refinementStateMap ρ B) (integral_refinementDensity M)).trans ?_
  simp [refinementStateMap, ρ.trace_eq_one]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
theorem refinedBornDensity_nonneg (M : MeasurablePOVM Ω I) (ρ : QIT.State I) (p : Ω × I) :
    0 ≤ M.refinedBornDensity ρ p :=
  mul_nonneg (Nat.cast_nonneg _)
    (QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten ρ.pos (M.refinementProjector_pos p.1 p.2))

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
theorem refinedBornDensity_le (M : MeasurablePOVM Ω I) (ρ : QIT.State I) (p : Ω × I) :
    M.refinedBornDensity ρ p ≤ (Fintype.card I : ℝ) := by
  have hp : M.refinementProjector p.1 p.2 ≤ 1 := by
    apply QIT.posSemidef_le_one_of_psdTracePower_le_one
      (M.refinementProjector_pos p.1 p.2) (q := 1) zero_lt_one
    rw [QIT.psdTracePower_one, M.refinementProjector_trace]
    norm_num
  have ht := QIT.cMatrix_trace_mul_le_of_le_posSemidef_right ρ.pos hp
  have htr : (ρ.matrix * M.refinementProjector p.1 p.2).trace.re ≤ 1 := by
    simpa only [Matrix.trace_mul_comm (M.refinementProjector p.1 p.2) ρ.matrix,
      Matrix.one_mul, ρ.trace_eq_one, Complex.one_re] using ht
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) htr

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
theorem refinedBornDensity_maximallyMixed (M : MeasurablePOVM Ω I) (p : Ω × I) :
    M.refinedBornDensity (QIT.State.maximallyMixed I) p = 1 := by
  simp [refinedBornDensity, QIT.State.maximallyMixed_matrix,
    Matrix.trace_smul, M.refinementProjector_trace, Fintype.card_ne_zero]

end RefinementMeasure

end LocalCertification.Quantum.MeasurablePOVM
