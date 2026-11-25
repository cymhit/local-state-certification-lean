import LocalCertification.Quantum.MeasurablePOVMRankOne
import LocalCertification.Quantum.MeasurablePOVMProduct

/-!
# Local rank-one refinement of arbitrary product POVMs

All original local outcome labels are retained. Forgetting only the auxiliary
finite spectral indices recovers the matrix effects, reference measure, and Born
law for every global state. The common refined density is the explicit tensor
product of the local rank-one projectors, scaled by the global dimension.
-/
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.Elementwise
noncomputable section
namespace LocalCertification.Quantum.MeasurablePOVM

/-- Forget only the finite refinement indices and retain every original outcome. -/
def productForget {ι α : Type*} {Ω : ι → Type*} (s : (i : ι) → Ω i × α) : (i : ι) → Ω i :=
  fun i => (s i).1

theorem productForget_measurable {ι α : Type*} [MeasurableSpace α]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] :
    Measurable (productForget (α := α) (Ω := Ω)) := by
  apply Measurable.of_eval
  intro i
  exact measurable_fst.comp (measurable_pi_apply i)

private theorem productForget_preimage_pi {ι α : Type*} {Ω : ι → Type*}
    (A : ∀ i, Set (Ω i)) :
    productForget (α := α) ⁻¹' (Set.univ.pi A) =
      Set.univ.pi (fun i => Prod.fst ⁻¹' A i) := by
  ext s
  simp [productForget]

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- The actual product of the actual local refined measurements. -/
def productRefined (M : ∀ i, MeasurablePOVM (Ω i) α) :
    MeasurablePOVM ((i : ι) → Ω i × α) (ι → α) := product (fun i => (M i).refinedPOVM)

/-- The same product of local reference probabilities for all global states. -/
def productRefinementReference (M : ∀ i, MeasurablePOVM (Ω i) α) :
    Measure ((i : ι) → Ω i × α) := Measure.pi (fun i => (M i).refinementReference)

instance productRefinementReference_probability (M : ∀ i, MeasurablePOVM (Ω i) α) :
    IsProbabilityMeasure (productRefinementReference M) := by
  unfold productRefinementReference
  infer_instance

theorem productRefined_traceReference (M : ∀ i, MeasurablePOVM (Ω i) α) :
    (productRefined M).traceReference = productRefinementReference M := by
  change (product (fun i => (M i).refinedPOVM)).traceReference = _
  rw [product_traceReference]
  simp only [refinedPOVM_traceReference, productRefinementReference]

/-- Matrix-valued pushforward, established first on rectangles and then on every event. -/
theorem productRefined_vectorMeasure_map (M : ∀ i, MeasurablePOVM (Ω i) α) :
    (productRefined M).toVectorMeasure.map productForget = (product M).toVectorMeasure := by
  let C : Set (Set ((i : ι) → Ω i)) :=
    Set.pi Set.univ '' Set.pi Set.univ (fun i => {s : Set (Ω i) | MeasurableSet s})
  have hgen : (inferInstance : MeasurableSpace ((i : ι) → Ω i)) =
      MeasurableSpace.generateFrom C := generateFrom_pi.symm
  refine VectorMeasure.ext_of_generateFrom C ?_ hgen isPiSystem_pi ?_
  · intro A hA
    rcases hA with ⟨B, hB, rfl⟩
    have hBm : ∀ i, MeasurableSet (B i) := fun i => hB i (Set.mem_univ i)
    rw [VectorMeasure.map_apply _ productForget_measurable (MeasurableSet.univ_pi hBm),
      productForget_preimage_pi]
    change (product (fun i => (M i).refinedPOVM)).toVectorMeasure _ = _
    rw [product_apply_pi _ _ (fun i => (hBm i).preimage measurable_fst), product_apply_pi _ B hBm]
    congr 1
    funext i
    exact (M i).refinedPOVM_apply_preimage_fst (hBm i)
  · rw [VectorMeasure.map_apply _ productForget_measurable MeasurableSet.univ,
      Set.preimage_univ, (productRefined M).univ, (product M).univ]

theorem productRefined_apply_preimage (M : ∀ i, MeasurablePOVM (Ω i) α)
    {A : Set ((i : ι) → Ω i)} (hA : MeasurableSet A) :
    (productRefined M).toVectorMeasure (productForget ⁻¹' A) = (product M).toVectorMeasure A := by
  have h := congrArg (fun v : VectorMeasure ((i : ι) → Ω i) (Matrix (ι → α) (ι → α) ℂ) => v A)
    (productRefined_vectorMeasure_map M)
  simpa only [VectorMeasure.map_apply _ productForget_measurable hA] using h

/-- The common refined reference marginal is the original product reference. -/
theorem productRefinementReference_map (M : ∀ i, MeasurablePOVM (Ω i) α) :
    (productRefinementReference M).map productForget = productReference M := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply productForget_measurable hA, ← productRefined_traceReference M,
    (productRefined M).traceReference_apply (hA.preimage productForget_measurable),
    productRefined_apply_preimage M hA, ← (product M).traceReference_apply hA,
    product_traceReference]
  rfl

/-- Every entangled or product state's original full outcome law is recovered. -/
theorem productRefined_born_map (M : ∀ i, MeasurablePOVM (Ω i) α) (ρ : QIT.State (ι → α)) :
    ((productRefined M).born ρ).map productForget = (product M).born ρ := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply productForget_measurable hA,
    (productRefined M).born_apply ρ (hA.preimage productForget_measurable),
    productRefined_apply_preimage M hA, (product M).born_apply ρ hA]

local instance localRefinementDensityContinuousENorm : ContinuousENorm (Matrix α α ℂ) :=
  SeminormedAddGroup.toContinuousENorm
local instance tensorRefinementDensityContinuousENorm :
    ContinuousENorm (Matrix (ι → α) (ι → α) ℂ) := SeminormedAddGroup.toContinuousENorm

omit [Fintype ι] [DecidableEq ι] in
private theorem localRefined_traceDensity_ae (i : ι) (M : MeasurablePOVM (Ω i) α) :
    M.refinedPOVM.traceDensity =ᵐ[M.refinementReference] M.refinementDensity := by
  have hi : Integrable M.refinedPOVM.traceDensity M.refinementReference := by
    rw [← M.refinedPOVM_traceReference]
    exact M.refinedPOVM.traceDensity_integrable
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi M.refinementDensity_integrable
  intro A hA _
  have h := M.refinedPOVM.traceDensity_setIntegral hA
  rw [M.refinedPOVM_traceReference] at h
  exact h.trans (M.refinedPOVM_apply hA)

/-- An explicit tensor projector; each factor is the local normalized rank-one term. -/
def productRefinementProjector (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) : Matrix (ι → α) (ι → α) ℂ :=
  tensorMatrix (fun i => (M i).refinementProjector (s i).1 (s i).2)

/-- The explicit tensor density against the common product reference. -/
def productRefinementDensity (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) : Matrix (ι → α) (ι → α) ℂ :=
  tensorMatrix (fun i => (M i).refinementDensity (s i))

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinementDensity_eq (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) :
    productRefinementDensity M s = (Fintype.card (ι → α) : ℝ) • productRefinementProjector M s := by
  ext x y
  simp only [productRefinementDensity, productRefinementProjector, tensorMatrix,
    refinementDensity, Matrix.smul_apply, Complex.real_smul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, Complex.ofReal_pow,
    Complex.ofReal_natCast]

omit [DecidableEq ι] in
private theorem productRefined_traceDensity_ae (M : ∀ i, MeasurablePOVM (Ω i) α) :
    productDensity (fun i => (M i).refinedPOVM) =ᵐ[productRefinementReference M]
      productRefinementDensity M := by
  have h := Measure.ae_eq_pi (μ := fun i => (M i).refinementReference)
    (fun i => localRefined_traceDensity_ae i (M i))
  filter_upwards [h] with s hs
  exact congrArg tensorMatrix hs

theorem productRefinementDensity_integrable (M : ∀ i, MeasurablePOVM (Ω i) α) :
    Integrable (productRefinementDensity M) (productRefinementReference M) := by
  have hi : Integrable (productDensity (fun i => (M i).refinedPOVM))
      (productRefinementReference M) := by
    simpa only [productReference, refinedPOVM_traceReference, productRefinementReference] using
      productDensity_integrable (fun i => (M i).refinedPOVM)
  exact hi.congr (productRefined_traceDensity_ae M)

/-- The actual refined product Born law has the explicit global-dimension tensor density. -/
theorem productRefined_born_eq_withDensity (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) :
    (productRefined M).born ρ = (productRefinementReference M).withDensity
      (fun s => ENNReal.ofReal ((Fintype.card (ι → α) : ℝ) *
        (ρ.matrix * tensorMatrix (fun i => (M i).refinementProjector (s i).1 (s i).2)).trace.re)) := by
  have h := product_born_eq_withDensity (fun i => (M i).refinedPOVM) ρ
  simp only [refinedPOVM_traceReference] at h
  refine h.trans (withDensity_congr_ae ?_)
  filter_upwards [productRefined_traceDensity_ae M] with s hs
  apply congrArg ENNReal.ofReal
  change (ρ.matrix * productDensity (fun i => (M i).refinedPOVM) s).trace.re = _
  rw [hs, productRefinementDensity_eq]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
    productRefinementProjector]

omit [DecidableEq ι] in
theorem productRefinementDensity_measurable (M : ∀ i, MeasurablePOVM (Ω i) α) :
    Measurable (productRefinementDensity M) := by
  apply Measurable.of_eval_matrix
  intro x y
  exact Finset.measurable_prod _ (fun i _ =>
    ((M i).refinementDensity_measurable.eval_matrix (i := x i) (j := y i)).comp
      (measurable_pi_apply i))

omit [DecidableEq ι] in
theorem productRefinementProjector_measurable (M : ∀ i, MeasurablePOVM (Ω i) α) :
    Measurable (productRefinementProjector M) := by
  have hp (i : ι) : Measurable (fun p : Ω i × α => (M i).refinementProjector p.1 p.2) :=
    measurable_from_prod_countable_left (M i).refinementProjector_measurable
  apply Measurable.of_eval_matrix
  intro x y
  exact Finset.measurable_prod _ (fun i _ =>
    ((hp i).eval_matrix (i := x i) (j := y i)).comp (measurable_pi_apply i))

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinementProjector_pos (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) : (productRefinementProjector M s).PosSemidef :=
  tensorMatrix_posSemidef _ (fun i => (M i).refinementProjector_pos (s i).1 (s i).2)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinementProjector_trace (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) : (productRefinementProjector M s).trace = 1 := by
  simp only [productRefinementProjector, tensorMatrix_trace, refinementProjector_trace,
    Finset.prod_const_one]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinementProjector_mul_self (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) :
    productRefinementProjector M s * productRefinementProjector M s = productRefinementProjector M s := by
  unfold productRefinementProjector
  rw [← tensorMatrix_mul]
  congr 1
  funext i
  exact (M i).refinementProjector_mul_self (s i).1 (s i).2

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinementDensity_pos (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) : (productRefinementDensity M s).PosSemidef :=
  tensorMatrix_posSemidef _ (fun i => (M i).refinementDensity_pos (s i))

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinementDensity_trace (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) : (productRefinementDensity M s).trace = (Fintype.card (ι → α) : ℂ) := by
  simp only [productRefinementDensity_eq, Matrix.trace_smul, productRefinementProjector_trace,
    Complex.real_smul, mul_one, Complex.ofReal_natCast]

theorem productRefinementDensity_setIntegral (M : ∀ i, MeasurablePOVM (Ω i) α)
    {A : Set ((i : ι) → Ω i × α)} (hA : MeasurableSet A) :
    ∫ s in A, productRefinementDensity M s ∂productRefinementReference M =
      (productRefined M).toVectorMeasure A := by
  have h := product_apply (fun i => (M i).refinedPOVM) hA
  simp only [productReference, refinedPOVM_traceReference] at h
  exact (integral_congr_ae (ae_restrict_of_ae (productRefined_traceDensity_ae M).symm)).trans h.symm

/-- The reference density of the refined product agrees almost everywhere with
the explicit tensor density. This identifies physical and frame integrals. -/
theorem productRefined_traceDensity_eq_tensor_ae (M : ∀ i, MeasurablePOVM (Ω i) α) :
    (productRefined M).traceDensity =ᵐ[productRefinementReference M] productRefinementDensity M := by
  have hi := (productRefined M).traceDensity_integrable
  rw [productRefined_traceReference] at hi
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi (productRefinementDensity_integrable M)
  intro A hA _
  have h := (productRefined M).traceDensity_setIntegral hA
  rw [productRefined_traceReference] at h
  exact h.trans (productRefinementDensity_setIntegral M hA).symm

theorem integral_productRefinementDensity (M : ∀ i, MeasurablePOVM (Ω i) α) :
    ∫ s, productRefinementDensity M s ∂productRefinementReference M = 1 := by
  simpa only [Measure.restrict_univ, (productRefined M).univ] using
    productRefinementDensity_setIntegral M MeasurableSet.univ

/-- The explicit scalar Born density of the local refinement product. -/
def productRefinedBornDensity (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) (s : (i : ι) → Ω i × α) : ℝ :=
  (ρ.matrix * productRefinementDensity M s).trace.re

private def productRefinementStateMap (ρ : QIT.State (ι → α)) :
    Matrix (ι → α) (ι → α) ℂ →L[ℝ] ℝ where
  toFun A := (ρ.matrix * A).trace.re
  map_add' _ _ := by simp [Matrix.mul_add]
  map_smul' _ _ := by simp
  cont := by fun_prop

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinedBornDensity_eq (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) (s : (i : ι) → Ω i × α) :
    productRefinedBornDensity M ρ s = (Fintype.card (ι → α) : ℝ) *
      (ρ.matrix * productRefinementProjector M s).trace.re := by
  simp only [productRefinedBornDensity, productRefinementDensity_eq, Matrix.mul_smul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem productRefinedBornDensity_measurable (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) : Measurable (productRefinedBornDensity M ρ) :=
  (productRefinementStateMap ρ).continuous.measurable.comp (productRefinementDensity_measurable M)

theorem productRefinedBornDensity_integrable (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) :
    Integrable (productRefinedBornDensity M ρ) (productRefinementReference M) :=
  (productRefinementStateMap ρ).integrable_comp (productRefinementDensity_integrable M)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinedBornDensity_nonneg (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) (s : (i : ι) → Ω i × α) :
    0 ≤ productRefinedBornDensity M ρ s :=
  QIT.cMatrix_trace_mul_posSemidef_re_nonneg_schatten ρ.pos (productRefinementDensity_pos M s)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinedBornDensity_le (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) (s : (i : ι) → Ω i × α) :
    productRefinedBornDensity M ρ s ≤ (Fintype.card (ι → α) : ℝ) := by
  have hρ : ρ.matrix ≤ 1 := by
    apply QIT.posSemidef_le_one_of_psdTracePower_le_one ρ.pos (q := 1) zero_lt_one
    rw [QIT.psdTracePower_one, ρ.trace_eq_one]
    norm_num
  have ht := QIT.cMatrix_trace_mul_le_of_le_posSemidef_right (productRefinementDensity_pos M s) hρ
  simpa only [productRefinedBornDensity, Matrix.one_mul, productRefinementDensity_trace,
    Complex.natCast_re] using ht

theorem integral_productRefinedBornDensity (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) :
    ∫ s, productRefinedBornDensity M ρ s ∂productRefinementReference M = 1 := by
  change (∫ s, productRefinementStateMap ρ (productRefinementDensity M s)
    ∂productRefinementReference M) = 1
  refine ((productRefinementStateMap ρ).integral_comp_comm (productRefinementDensity_integrable M)).trans ?_
  refine (congrArg (fun B => productRefinementStateMap ρ B) (integral_productRefinementDensity M)).trans ?_
  simp [productRefinementStateMap, ρ.trace_eq_one]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinedBornDensity_maximallyMixed (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) :
    productRefinedBornDensity M (QIT.State.maximallyMixed (ι → α)) s = 1 := by
  simp [productRefinedBornDensity, QIT.State.maximallyMixed_matrix, Matrix.trace_smul,
    productRefinementDensity_trace, Fintype.card_ne_zero]

theorem productRefined_born_eq_density (M : ∀ i, MeasurablePOVM (Ω i) α)
    (ρ : QIT.State (ι → α)) :
    (productRefined M).born ρ = (productRefinementReference M).withDensity
      (fun s => ENNReal.ofReal (productRefinedBornDensity M ρ s)) := by
  simpa only [productRefinedBornDensity_eq, productRefinementProjector] using
    productRefined_born_eq_withDensity M ρ

omit [DecidableEq ι] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinementProjector_eq_rankOne (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) :
    ∃ v : (ι → α) → ℂ, productRefinementProjector M s = QIT.rankOneMatrix v := by
  classical
  choose ψ hψ using fun i => (M i).refinementProjector_eq_pure (s i).1 (s i).2
  have hp (i : ι) : (M i).refinementProjector (s i).1 (s i).2 = QIT.rankOneMatrix (ψ i).amp :=
    (hψ i).symm
  refine ⟨fun x => ∏ i, (ψ i).amp (x i), ?_⟩
  ext x y
  simp only [productRefinementProjector, tensorMatrix, hp, QIT.rankOneMatrix_apply,
    star_prod, Finset.prod_mul_distrib]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem productRefinementProjector_rank (M : ∀ i, MeasurablePOVM (Ω i) α)
    (s : (i : ι) → Ω i × α) : (productRefinementProjector M s).rank ≤ 1 := by
  obtain ⟨v, hv⟩ := productRefinementProjector_eq_rankOne M s
  rw [hv]
  exact QIT.rankOneMatrix_rank_le_one v

end LocalCertification.Quantum.MeasurablePOVM
