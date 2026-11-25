import LocalCertification.Quantum.MeasurablePOVM
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Matrix densities of measurable POVMs

The reference measure is the normalized trace measure. Scalar signed-measure
Radon–Nikodym derivatives give the matrix entries on arbitrary measurable
outcome spaces.
-/

set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace LocalCertification.Quantum.MeasurablePOVM

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Nonempty I]

local instance : ContinuousENorm (Matrix I I ℂ) := SeminormedAddGroup.toContinuousENorm

private def scalarMeasure (M : MeasurablePOVM Ω I) (f : Matrix I I ℂ →L[ℝ] ℝ) :
    SignedMeasure Ω := M.toVectorMeasure.mapRange f.toAddMonoidHom f.continuous

private theorem scalarMeasure_ac (M : MeasurablePOVM Ω I) (f : Matrix I I ℂ →L[ℝ] ℝ) :
    scalarMeasure M f ≪ᵥ M.traceReference.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro A hA hz
  rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hz
  change f (M.toVectorMeasure A) = 0
  rw [(M.traceReference_eq_zero_iff hA).mp hz, map_zero]

private def scalarDensity (M : MeasurablePOVM Ω I) (f : Matrix I I ℂ →L[ℝ] ℝ) : Ω → ℝ :=
  (scalarMeasure M f).rnDeriv M.traceReference

omit [Nonempty I] in
private theorem scalarDensity_measurable (M : MeasurablePOVM Ω I)
    (f : Matrix I I ℂ →L[ℝ] ℝ) : Measurable (scalarDensity M f) :=
  SignedMeasure.measurable_rnDeriv _ _

omit [Nonempty I] in
private theorem scalarDensity_integrable (M : MeasurablePOVM Ω I)
    (f : Matrix I I ℂ →L[ℝ] ℝ) : Integrable (scalarDensity M f) M.traceReference :=
  SignedMeasure.integrable_rnDeriv _ _

private theorem scalarDensity_setIntegral (M : MeasurablePOVM Ω I)
    (f : Matrix I I ℂ →L[ℝ] ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ s in A, scalarDensity M f s ∂M.traceReference = f (M.toVectorMeasure A) := by
  have h := congrArg (fun v : SignedMeasure Ω => v A)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq (scalarMeasure M f) M.traceReference
      (scalarMeasure_ac M f))
  change (M.traceReference.withDensityᵥ (scalarDensity M f)) A =
    f (M.toVectorMeasure A) at h
  rw [withDensityᵥ_apply (scalarDensity_integrable M f) hA] at h
  exact h

private def entryRe (i j : I) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (A i j).re
  map_add' A B := by simp
  map_smul' r A := by simp
  cont := by fun_prop

private def entryIm (i j : I) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (A i j).im
  map_add' A B := by simp
  map_smul' r A := by simp
  cont := by fun_prop

private def rawDensity (M : MeasurablePOVM Ω I) (s : Ω) : Matrix I I ℂ :=
  fun i j => ⟨scalarDensity M (entryRe i j) s, scalarDensity M (entryIm i j) s⟩

omit [Nonempty I] in
private theorem rawDensity_measurable (M : MeasurablePOVM Ω I) : Measurable (rawDensity M) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun s => Complex.mk (scalarDensity M (entryRe i j) s)
    (scalarDensity M (entryIm i j) s))
  have hr := scalarDensity_measurable M (entryRe i j)
  have hi := scalarDensity_measurable M (entryIm i j)
  exact Complex.equivRealProdCLM.symm.continuous.measurable.comp (hr.prodMk hi)

omit [Nonempty I] in
private theorem rawDensity_integrable (M : MeasurablePOVM Ω I) :
    Integrable (rawDensity M) M.traceReference := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  exact Integrable.re_im_iff.mp
    ⟨scalarDensity_integrable M (entryRe i j), scalarDensity_integrable M (entryIm i j)⟩

private theorem rawDensity_setIntegral (M : MeasurablePOVM Ω I)
    {A : Set Ω} (hA : MeasurableSet A) :
    ∫ s in A, rawDensity M s ∂M.traceReference = M.toVectorMeasure A := by
  ext i j
  apply Complex.ext
  · change entryRe i j (∫ s in A, rawDensity M s ∂M.traceReference) = _
    exact ((entryRe i j).integral_comp_comm
      (μ := M.traceReference.restrict A) (rawDensity_integrable M).integrableOn).symm.trans
      (scalarDensity_setIntegral M (entryRe i j) hA)
  · change entryIm i j (∫ s in A, rawDensity M s ∂M.traceReference) = _
    exact ((entryIm i j).integral_comp_comm
      (μ := M.traceReference.restrict A) (rawDensity_integrable M).integrableOn).symm.trans
      (scalarDensity_setIntegral M (entryIm i j) hA)

private def adjointCLM : Matrix I I ℂ →L[ℝ] Matrix I I ℂ where
  toFun A := A.conjTranspose
  map_add' A B := Matrix.conjTranspose_add A B
  map_smul' r A := by simp
  cont := by fun_prop

private theorem rawDensity_hermitian_ae (M : MeasurablePOVM Ω I) :
    ∀ᵐ s ∂M.traceReference, (rawDensity M s).IsHermitian := by
  have h := Integrable.ae_eq_of_forall_setIntegral_eq
    (fun s => adjointCLM (rawDensity M s)) (rawDensity M)
    (adjointCLM.integrable_comp (rawDensity_integrable M)) (rawDensity_integrable M)
    (fun A hA _ =>
      (adjointCLM.integral_comp_comm (μ := M.traceReference.restrict A)
          (rawDensity_integrable M).integrableOn).trans
        ((congrArg (fun B => adjointCLM B) (rawDensity_setIntegral M hA)).trans
          ((M.positive A hA).isHermitian.eq.trans (rawDensity_setIntegral M hA).symm)))
  exact h

private def quadraticRe (v : I → ℂ) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (star v ⬝ᵥ (A *ᵥ v)).re
  map_add' A B := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' r A := by simp [Matrix.smul_mulVec, dotProduct_smul]
  cont := by
    unfold Matrix.mulVec dotProduct
    fun_prop

private theorem rawDensity_quadratic_ae (M : MeasurablePOVM Ω I) (v : I → ℂ) :
    ∀ᵐ s ∂M.traceReference, 0 ≤ quadraticRe v (rawDensity M s) := by
  apply ae_nonneg_of_forall_setIntegral_nonneg
    ((quadraticRe v).integrable_comp (rawDensity_integrable M))
  intro A hA _
  rw [(quadraticRe v).integral_comp_comm (rawDensity_integrable M).integrableOn,
    rawDensity_setIntegral M hA]
  exact (M.positive A hA).re_dotProduct_nonneg v

private theorem rawDensity_pos_ae (M : MeasurablePOVM Ω I) :
    ∀ᵐ s ∂M.traceReference, (rawDensity M s).PosSemidef := by
  have hall : ∀ᵐ s ∂M.traceReference, ∀ n : ℕ,
      0 ≤ quadraticRe (TopologicalSpace.denseSeq (I → ℂ) n) (rawDensity M s) :=
    ae_all_iff.mpr (fun n => rawDensity_quadratic_ae M _)
  filter_upwards [rawDensity_hermitian_ae M, hall] with s hH hn
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  have hv : 0 ≤ quadraticRe v (rawDensity M s) := by
    have hc : Continuous (fun v : I → ℂ => quadraticRe v (rawDensity M s)) := by
      change Continuous (fun v : I → ℂ => (star v ⬝ᵥ (rawDensity M s *ᵥ v)).re)
      unfold Matrix.mulVec dotProduct
      fun_prop
    exact (TopologicalSpace.denseRange_denseSeq (I → ℂ)).induction_on
      (p := fun v => 0 ≤ quadraticRe v (rawDensity M s)) v
      (isClosed_le continuous_const hc) hn
  exact ⟨hv, (hH.im_star_dotProduct_mulVec_self v).symm⟩

private def traceCLM : Matrix I I ℂ →L[ℝ] ℂ where
  toFun A := A.trace
  map_add' A B := Matrix.trace_add A B
  map_smul' r A := Matrix.trace_smul r A
  cont := by fun_prop

private theorem effect_trace (M : MeasurablePOVM Ω I) {A : Set Ω} (hA : MeasurableSet A) :
    (M.toVectorMeasure A).trace = M.traceReference.real A • (Fintype.card I : ℂ) := by
  have hd : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hr : M.traceReference.real A = (M.toVectorMeasure A).trace.re / Fintype.card I := by
    rw [measureReal_def, traceReference_apply M hA, ENNReal.toReal_ofReal]
    exact div_nonneg (M.positive A hA).trace_nonneg.1 (Nat.cast_nonneg _)
  apply Complex.ext
  · simp only [Complex.smul_re, Complex.natCast_re, smul_eq_mul]
    rw [hr, div_mul_cancel₀ _ hd]
  · simpa using (M.positive A hA).trace_nonneg.2.symm

private theorem rawDensity_trace_ae (M : MeasurablePOVM Ω I) :
    ∀ᵐ s ∂M.traceReference, (rawDensity M s).trace = (Fintype.card I : ℂ) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq
    (fun s => traceCLM (rawDensity M s)) (fun _ => (Fintype.card I : ℂ))
    (traceCLM.integrable_comp (rawDensity_integrable M)) (integrable_const _)
  intro A hA _
  refine (traceCLM.integral_comp_comm (μ := M.traceReference.restrict A)
    (rawDensity_integrable M).integrableOn).trans ?_
  refine (congrArg (fun B => traceCLM B) (rawDensity_setIntegral M hA)).trans ?_
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
    traceCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using effect_trace M hA

/-- The normalized trace reference has a measurable matrix RN density. The null-set
representative is chosen to be positive with trace equal to the dimension everywhere. -/
theorem exists_traceDensity (M : MeasurablePOVM Ω I) :
    ∃ K : Ω → Matrix I I ℂ,
      Measurable K ∧ Integrable K M.traceReference ∧
      (∀ s, (K s).PosSemidef ∧ (K s).trace = (Fintype.card I : ℂ)) ∧
      M.toVectorMeasure = M.traceReference.withDensityᵥ K := by
  classical
  have hgood := (rawDensity_pos_ae M).and (rawDensity_trace_ae M)
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  let K : Ω → Matrix I I ℂ := N.piecewise (fun _ => 1) (rawDensity M)
  have heq : K =ᵐ[M.traceReference] rawDensity M := by
    have hn : ∀ᵐ s ∂M.traceReference, s ∉ N := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using hNzero
    filter_upwards [hn] with s hs
    exact Set.piecewise_eq_of_notMem N (fun _ => 1) (rawDensity M) hs
  refine ⟨K, measurable_const.piecewise hNm (rawDensity_measurable M),
    (rawDensity_integrable M).congr heq.symm, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ N
    · simp only [K, Set.piecewise_eq_of_mem N (fun _ => 1) (rawDensity M) hs]
      exact ⟨Matrix.PosSemidef.one, by simp⟩
    · simp only [K, Set.piecewise_eq_of_notMem N (fun _ => 1) (rawDensity M) hs]
      by_contra hb
      exact hs (hNsub hb)
  · apply VectorMeasure.ext
    intro A hA
    exact (rawDensity_setIntegral M hA).symm.trans
      ((integral_congr_ae (ae_restrict_of_ae heq.symm)).trans
        (withDensityᵥ_apply ((rawDensity_integrable M).congr heq.symm) hA).symm)

/-- A measurable representative of the matrix density, positive with fixed trace everywhere. -/
def traceDensity (M : MeasurablePOVM Ω I) : Ω → Matrix I I ℂ :=
  Classical.choose M.exists_traceDensity

theorem traceDensity_measurable (M : MeasurablePOVM Ω I) : Measurable M.traceDensity :=
  (Classical.choose_spec M.exists_traceDensity).1

theorem traceDensity_integrable (M : MeasurablePOVM Ω I) :
    Integrable M.traceDensity M.traceReference :=
  (Classical.choose_spec M.exists_traceDensity).2.1

theorem traceDensity_pos (M : MeasurablePOVM Ω I) (s : Ω) : (M.traceDensity s).PosSemidef :=
  ((Classical.choose_spec M.exists_traceDensity).2.2.1 s).1

theorem traceDensity_trace (M : MeasurablePOVM Ω I) (s : Ω) :
    (M.traceDensity s).trace = (Fintype.card I : ℂ) :=
  ((Classical.choose_spec M.exists_traceDensity).2.2.1 s).2

theorem traceDensity_reconstruct (M : MeasurablePOVM Ω I) :
    M.toVectorMeasure = M.traceReference.withDensityᵥ M.traceDensity :=
  (Classical.choose_spec M.exists_traceDensity).2.2.2

theorem traceDensity_setIntegral (M : MeasurablePOVM Ω I) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ s in A, M.traceDensity s ∂M.traceReference = M.toVectorMeasure A :=
  (withDensityᵥ_apply M.traceDensity_integrable hA).symm.trans
    (congrArg (fun v : VectorMeasure Ω (Matrix I I ℂ) => v A) M.traceDensity_reconstruct).symm

private def stateCLM (ρ : QIT.State I) : Matrix I I ℂ →L[ℝ] ℝ where
  toFun A := (ρ.matrix * A).trace.re
  map_add' A B := by simp [Matrix.mul_add]
  map_smul' r A := by simp
  cont := by fun_prop

/-- The same matrix density gives the Born law for every quantum state. -/
theorem born_eq_withDensity_traceDensity (M : MeasurablePOVM Ω I) (ρ : QIT.State I) :
    M.born ρ = M.traceReference.withDensity
      (fun s => ENNReal.ofReal ((ρ.matrix * M.traceDensity s).trace.re)) := by
  apply Measure.ext
  intro A hA
  rw [M.born_apply ρ hA, withDensity_apply _ hA]
  have hi := (stateCLM ρ).integrable_comp M.traceDensity_integrable
  have hn : ∀ s, 0 ≤ stateCLM ρ (M.traceDensity s) := fun s =>
    QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten ρ.pos (M.traceDensity_pos s)
  calc
    ENNReal.ofReal ((ρ.matrix * M.toVectorMeasure A).trace.re) =
        ENNReal.ofReal (∫ s in A, stateCLM ρ (M.traceDensity s) ∂M.traceReference) := by
      apply congrArg ENNReal.ofReal
      exact ((stateCLM ρ).integral_comp_comm (μ := M.traceReference.restrict A)
        M.traceDensity_integrable.integrableOn).trans
          (congrArg (fun B => stateCLM ρ B) (M.traceDensity_setIntegral hA)) |>.symm
    _ = _ := ofReal_integral_eq_lintegral_ofReal hi.integrableOn
      (Filter.Eventually.of_forall hn)

end LocalCertification.Quantum.MeasurablePOVM
