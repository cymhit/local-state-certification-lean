import CertificationGaussian.ComplexTensorFrame
import CertificationGaussian.CanonicalComplexFrameNet

/-! # Physical tensor frames and the signed residual map

The coordinate tensor frame is transported to the original matrix HS space.
Applying the actual complement operator gives the actual signed-kernel frame.
The resulting perturbation estimate has the sphere-score scale D².
-/

noncomputable section
open MeasureTheory Matrix Metric
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

theorem integralComplexHilbertFrame_isometry
    {Ω E F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Ω → E) (hV : AEStronglyMeasurable V ν)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖V s‖ ≤ K) (e : E ≃ₗᵢ[ℂ] F) :
    integralComplexHilbertFrame ν (fun s => e (V s)) =
      (e : E →L[ℂ] F).comp ((integralComplexHilbertFrame ν V).comp (e.symm : F →L[ℂ] E)) := by
  have hEV := e.continuous.comp_aestronglyMeasurable hV
  have hEb : ∀ᵐ s ∂ν, ‖e (V s)‖ ≤ K := by simpa only [LinearIsometryEquiv.norm_map] using hbound
  have hleft (v : E) (x : F) : inner ℂ (e v) x = inner ℂ v (e.symm x) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using e.inner_map_map v (e.symm x)
  have hright (y : F) (v : E) : inner ℂ y (e v) = inner ℂ (e.symm y) v := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using e.inner_map_map (e.symm y) v
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [integralComplexHilbertFrame_inner ν _ hEV hK hEb]
  change (∫ s, inner ℂ (e (V s)) x * inner ℂ y (e (V s)) ∂ν) =
    inner ℂ y (e (integralComplexHilbertFrame ν V (e.symm x)))
  rw [hright, integralComplexHilbertFrame_inner ν V hV hK hbound]
  simp only [hleft, hright]

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

def complexProductMatrixFrame (T : S → ComplexMatrixFrameSpace I) : ComplexMatrixFrameSpace (S → I) :=
  ((matrixTensorCoordinateEquiv (S := S) (I := I)).symm : _ →L[ℂ] _).comp
    ((coordinateSubsetLift Finset.univ T).comp
      (matrixTensorCoordinateEquiv (S := S) (I := I) : _ →L[ℂ] _))

theorem complexProductMatrixFrame_distance_le (T U : S → ComplexMatrixFrameSpace I) :
    ‖complexProductMatrixFrame T-complexProductMatrixFrame U‖ ≤
      ‖coordinateSubsetLift Finset.univ T-coordinateSubsetLift Finset.univ U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖matrixTensorCoordinateEquiv.symm (coordinateSubsetLift Finset.univ T (matrixTensorCoordinateEquiv x))-
    matrixTensorCoordinateEquiv.symm (coordinateSubsetLift Finset.univ U (matrixTensorCoordinateEquiv x))‖ ≤ _
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  simpa only [_root_.sub_apply, LinearIsometryEquiv.norm_map] using
    (coordinateSubsetLift Finset.univ T-coordinateSubsetLift Finset.univ U).le_opNorm (matrixTensorCoordinateEquiv x)

theorem complexProductMatrixFrame_norm_le (T : S → ComplexMatrixFrameSpace I) {c : ℝ}
    (hc : 0 ≤ c) (hT : ∀ s, ‖T s‖ ≤ c) :
    ‖complexProductMatrixFrame T‖ ≤ c^(Fintype.card S) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hc _)
  intro x
  change ‖matrixTensorCoordinateEquiv.symm (coordinateSubsetLift Finset.univ T (matrixTensorCoordinateEquiv x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h := (coordinateSubsetLift Finset.univ T).le_opNorm (matrixTensorCoordinateEquiv x)
  rw [LinearIsometryEquiv.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (by simpa only [Finset.card_univ] using coordinateSubsetLift_norm_le_pow Finset.univ T hc hT) (norm_nonneg _))

theorem complexProductMatrixFrame_adjoint (T : S → ComplexMatrixFrameSpace I) :
    ContinuousLinearMap.adjoint (complexProductMatrixFrame T) =
      complexProductMatrixFrame (fun s => ContinuousLinearMap.adjoint (T s)) := by
  simp only [complexProductMatrixFrame, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm,
    coordinateSubsetLift_adjoint, ContinuousLinearMap.comp_assoc]

section ActualProduct
variable {Ω : S → Type*} [∀ s, MeasurableSpace (Ω s)]
  (ν : (s : S) → Measure (Ω s)) [∀ s, IsProbabilityMeasure (ν s)]
  (P : (s : S) → Ω s → Matrix I I ℂ) (hm : ∀ s, Measurable (P s))
  (hn : ∀ s t, ‖matrixHilbertSchmidt (P s t)‖ = 1)
include hm hn

omit [DecidableEq I] hn in
private theorem productHS_measurable : Measurable
    (fun ω : (s : S) → Ω s => matrixHilbertSchmidt (wickTensorMatrix (fun s => P s (ω s)))) := by
  have hV (s : S) : Measurable (fun t => matrixHilbertSchmidt (P s t)) := by
    have hc : Continuous (matrixHilbertSchmidt : Matrix I I ℂ → EuclideanSpace ℂ (I × I)) := by
      unfold matrixHilbertSchmidt
      fun_prop
    exact hc.measurable.comp (hm s)
  have h := (matrixTensorCoordinateEquiv (S := S) (I := I)).symm.continuous.measurable.comp
    (productUnitVector_measurable (fun s t => matrixHilbertSchmidt (P s t)) hV)
  convert h using 1
  funext ω
  exact ((matrixTensorCoordinateEquiv (S := S) (I := I)).symm_apply_apply
    (matrixHilbertSchmidt (wickTensorMatrix (fun s => P s (ω s))))).symm

omit [DecidableEq I] [∀ s, MeasurableSpace (Ω s)] hm in
private theorem productHS_unit (ω : (s : S) → Ω s) :
    ‖matrixHilbertSchmidt (wickTensorMatrix (fun s => P s (ω s)))‖ = 1 := by
  rw [← (matrixTensorCoordinateEquiv (S := S) (I := I)).norm_map,
    matrixTensorCoordinateEquiv_tensor]
  exact tensorCoordinateVector_unit (fun s => matrixHilbertSchmidt (P s (ω s))) (fun s => hn s (ω s))

theorem integralComplexMatrixFrame_product :
    integralComplexMatrixFrame (Measure.pi ν) (fun ω => wickTensorMatrix (fun s => P s (ω s))) =
      complexProductMatrixFrame (fun s => integralComplexMatrixFrame (ν s) (P s)) := by
  let e := matrixTensorCoordinateEquiv (S := S) (I := I)
  let V := fun ω : (s : S) → Ω s => matrixHilbertSchmidt (wickTensorMatrix (fun s => P s (ω s)))
  have h := integralComplexHilbertFrame_isometry (Measure.pi ν) V
    (productHS_measurable P hm).aestronglyMeasurable (by norm_num : (0:ℝ) ≤ 1)
    (ae_of_all _ fun ω => (productHS_unit P hn ω).le) e
  have hV (s : S) : Measurable (fun t => matrixHilbertSchmidt (P s t)) := by
    have hc : Continuous (matrixHilbertSchmidt : Matrix I I ℂ → EuclideanSpace ℂ (I × I)) := by
      unfold matrixHilbertSchmidt
      fun_prop
    exact hc.measurable.comp (hm s)
  change integralComplexHilbertFrame (Measure.pi ν)
    (fun ω => tensorCoordinateVector (fun s => matrixHilbertSchmidt (P s (ω s)))) = _ at h
  rw [integralComplexHilbertFrame_tensor ν _ hV hn] at h
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun L => e.symm (L (e x))) h
  change e.symm ((coordinateSubsetLift Finset.univ
    (fun s => integralComplexHilbertFrame (ν s) (fun t => matrixHilbertSchmidt (P s t)))) (e x)) =
      e.symm (e (integralComplexHilbertFrame (Measure.pi ν) V (e.symm (e x)))) at hx
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply] at hx
  exact hx.symm

end ActualProduct

def signedProductMatrixFrame (J : Finset ℕ) (θ : ℕ → ℝ) (T : S → ComplexMatrixFrameSpace I) :
    ComplexMatrixFrameSpace (S → I) :=
  (cardinalityComplementOperator J θ).comp ((complexProductMatrixFrame T).comp
    (cardinalityComplementOperator J θ))

/-- The signed operator is the frame of the original literal signed kernel. -/
theorem integralComplexMatrixFrame_signedProduct
    {Ω : S → Type*} [∀ s, MeasurableSpace (Ω s)]
    (ν : (s : S) → Measure (Ω s)) [∀ s, IsProbabilityMeasure (ν s)]
    (P : (s : S) → Ω s → Matrix I I ℂ) (hm : ∀ s, Measurable (P s))
    (hn : ∀ s t, ‖matrixHilbertSchmidt (P s t)‖ = 1)
    (ht : ∀ s t, (P s t).trace = 1) (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) :
    integralComplexMatrixFrame (Measure.pi ν)
      (fun ω => cardinalityProjectorKernel (fun s => P s (ω s)) J θ) =
      signedProductMatrixFrame J θ (fun s => integralComplexMatrixFrame (ν s) (P s)) := by
  have he : (fun ω : (s : S) → Ω s =>
      matrixHilbertSchmidt (cardinalityProjectorKernel (fun s => P s (ω s)) J θ)) =
      fun ω => cardinalityComplementOperator J θ
        (matrixHilbertSchmidt (wickTensorMatrix (fun s => P s (ω s)))) := by
    funext ω
    exact (cardinalityComplementOperator_matrix hd J θ _ (fun s => ht s (ω s))).symm
  change integralComplexHilbertFrame (Measure.pi ν) _ = _
  rw [he, integralComplexHilbertFrame_map (Measure.pi ν) _
    (productHS_measurable P hm).aestronglyMeasurable (by norm_num : (0:ℝ) ≤ 1)
    (ae_of_all _ fun ω => (productHS_unit P hn ω).le)]
  change (cardinalityComplementOperator J θ).comp
    ((integralComplexMatrixFrame (Measure.pi ν) (fun ω => wickTensorMatrix (fun s => P s (ω s)))).comp
      (ContinuousLinearMap.adjoint (cardinalityComplementOperator J θ))) = _
  rw [integralComplexMatrixFrame_product ν P hm hn, cardinalityComplementOperator_adjoint]
  rfl

theorem signedProductMatrixFrame_adjoint (J : Finset ℕ) (θ : ℕ → ℝ)
    (T : S → ComplexMatrixFrameSpace I) :
    ContinuousLinearMap.adjoint (signedProductMatrixFrame J θ T) =
      signedProductMatrixFrame J θ (fun s => ContinuousLinearMap.adjoint (T s)) := by
  simp only [signedProductMatrixFrame, ContinuousLinearMap.adjoint_comp,
    cardinalityComplementOperator_adjoint, complexProductMatrixFrame_adjoint,
    ContinuousLinearMap.comp_assoc]

omit [DecidableEq S] [DecidableEq I] [Fintype S] in
theorem complexMatrixFrame_restrict_symmetric (T : ComplexMatrixFrameSpace I)
    (hT : ContinuousLinearMap.adjoint T = T) (X Y : EuclideanSpace ℂ (I × I)) :
    inner ℝ X (T.restrictScalars ℝ Y) = inner ℝ (T.restrictScalars ℝ X) Y := by
  have hr (a b : EuclideanSpace ℂ (I × I)) : inner ℝ a b = (inner ℂ a b).re := by
    change (∑ i, (b i*star (a i)).re) = (∑ i, b i*star (a i)).re
    rw [Complex.re_sum]
  rw [hr, hr]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have h := ContinuousLinearMap.adjoint_inner_left T Y X
  rw [hT] at h
  exact congrArg Complex.re h.symm

omit [Fintype S] [DecidableEq S] in
theorem matrixHilbertSchmidt_unitProjector_norm (u : EuclideanSpace ℂ I) (hu : ‖u‖ = 1) :
    ‖matrixHilbertSchmidt (vectorRankOne u u)‖ = 1 := by
  have h : ‖matrixHilbertSchmidt (vectorRankOne u u)‖^2 = 1 := by
    rw [matrixHilbertSchmidt_norm_sq _ (vectorRankOne_self_hermitian _),
      vectorRankOne_self_sq _ hu, vectorRankOne_self_trace _ hu, Complex.one_re]
  nlinarith [norm_nonneg (matrixHilbertSchmidt (vectorRankOne u u))]

omit [Fintype S] [DecidableEq S] in
theorem canonicalRankOneFrame_adjoint (T : canonicalRankOneFrames (I := I)) :
    ContinuousLinearMap.adjoint T.val = T.val := by
  obtain ⟨η, hη, _, heq⟩ := T.property
  let := hη
  rw [heq]
  have hc : Continuous (fun ψ : Metric.sphere (0 : EuclideanSpace ℂ I) 1 =>
      matrixHilbertSchmidt (vectorRankOne ψ.val ψ.val)) := by
    unfold matrixHilbertSchmidt vectorRankOne
    fun_prop
  exact integralComplexHilbertFrame_adjoint η _ hc.measurable.aestronglyMeasurable
    (by norm_num : (0:ℝ) ≤ 1) (ae_of_all _ fun ψ =>
      (matrixHilbertSchmidt_unitProjector_norm ψ.val (mem_sphere_zero_iff_norm.mp ψ.property)).le)

theorem signedProductMatrixFrame_distance_le (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (T U : S → ComplexMatrixFrameSpace I)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ s, ‖T s‖ ≤ (Fintype.card I : ℝ)⁻¹)
    (hU : ∀ s, ‖U s‖ ≤ (Fintype.card I : ℝ)⁻¹)
    (hclose : ∀ s, ‖T s-U s‖ ≤ ε) :
    ‖signedProductMatrixFrame J θ T-signedProductMatrixFrame J θ U‖ ≤
      (∑ k ∈ J, |θ k|)^2 * ((Fintype.card S : ℝ)*ε*(Fintype.card I : ℝ)⁻¹^(Fintype.card S-1)) := by
  let R := cardinalityComplementOperator (S := S) (I := I) J θ
  let L := ∑ k ∈ J, |θ k|
  have hR : ‖R‖ ≤ L := cardinalityComplementOperator_norm_le hd J θ
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have he : signedProductMatrixFrame J θ T-signedProductMatrixFrame J θ U =
      R.comp ((complexProductMatrixFrame T-complexProductMatrixFrame U).comp R) := by
    ext x
    simp [signedProductMatrixFrame, R]
  rw [he]
  calc
    _ ≤ ‖R‖*(‖complexProductMatrixFrame T-complexProductMatrixFrame U‖*‖R‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖R‖^2 * ‖complexProductMatrixFrame T-complexProductMatrixFrame U‖ := by ring
    _ ≤ L^2 * ((Fintype.card S : ℝ)*ε*(Fintype.card I : ℝ)⁻¹^(Fintype.card S-1)) :=
      mul_le_mul ((sq_le_sq₀ (norm_nonneg _) hL).mpr hR)
        ((complexProductMatrixFrame_distance_le T U).trans
          (coordinateTensorFrame_distance_le T U (by positivity) hε hT hU hclose))
        (norm_nonneg _) (sq_nonneg _)

theorem signedProductMatrixFrame_scaled_distance_le (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (T U : S → ComplexMatrixFrameSpace I)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ s, ‖T s‖ ≤ (Fintype.card I : ℝ)⁻¹)
    (hU : ∀ s, ‖U s‖ ≤ (Fintype.card I : ℝ)⁻¹)
    (hclose : ∀ s, ‖T s-U s‖ ≤ ε) :
    ((Fintype.card I : ℝ)^(Fintype.card S))^2 *
      ‖signedProductMatrixFrame J θ T-signedProductMatrixFrame J θ U‖ ≤
      (Fintype.card I : ℝ)*(Fintype.card I : ℝ)^(Fintype.card S)*
        (∑ k ∈ J, |θ k|)^2*(Fintype.card S : ℝ)*ε := by
  have h := mul_le_mul_of_nonneg_left
    (signedProductMatrixFrame_distance_le hd J θ T U hε hT hU hclose)
    (sq_nonneg ((Fintype.card I : ℝ)^(Fintype.card S)))
  apply h.trans_eq
  by_cases hn : Fintype.card S = 0
  · simp [hn]
  · have hd0 : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card I ≠ 0)
    have hn' : Fintype.card S = (Fintype.card S-1)+1 := by omega
    have hp : ((Fintype.card I : ℝ)^(Fintype.card S))^2 *
        (Fintype.card I : ℝ)⁻¹^(Fintype.card S-1) =
        (Fintype.card I : ℝ)*(Fintype.card I : ℝ)^(Fintype.card S) := by
      conv_lhs => arg 1; rw [hn', pow_succ]
      conv_rhs => arg 2; rw [hn', pow_succ]
      rw [inv_pow]
      field_simp
      ring
    calc
      _ = (((Fintype.card I : ℝ)^(Fintype.card S))^2 *
          (Fintype.card I : ℝ)⁻¹^(Fintype.card S-1)) *
          (∑ k ∈ J, |θ k|)^2*(Fintype.card S : ℝ)*ε := by ring
      _ = _ := by rw [hp]

theorem exists_signedProductFrame_distance (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (T U : S → ComplexMatrixFrameSpace I)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hT : ∀ s, ‖T s‖ ≤ (Fintype.card I : ℝ)⁻¹)
    (hU : ∀ s, ‖U s‖ ≤ (Fintype.card I : ℝ)⁻¹)
    (hclose : ∀ s, ‖T s-U s‖ ≤ ε) :
    ∃ F : (S → ComplexMatrixFrameSpace I) → ComplexMatrixFrameSpace (S → I),
      (∀ V, F V = (cardinalityComplementOperator J θ).comp
        ((((matrixTensorCoordinateEquiv (S := S) (I := I)).symm : _ →L[ℂ] _).comp
          ((coordinateSubsetLift Finset.univ V).comp
            (matrixTensorCoordinateEquiv (S := S) (I := I) : _ →L[ℂ] _))).comp
              (cardinalityComplementOperator J θ))) ∧
      ((Fintype.card I : ℝ)^(Fintype.card S))^2 * ‖F T-F U‖ ≤
        (Fintype.card I : ℝ)*(Fintype.card I : ℝ)^(Fintype.card S)*
          (∑ k ∈ J, |θ k|)^2*(Fintype.card S : ℝ)*ε :=
  ⟨signedProductMatrixFrame J θ, fun _ => rfl,
    signedProductMatrixFrame_scaled_distance_le hd J θ T U hε hT hU hclose⟩

end CertificationGaussian
