import CertificationGaussian.HilbertCoordinateLift
import CertificationGaussian.ProjectorComplementKernel
import CertificationGaussian.CardinalityProjectorKernel
import Mathlib.Data.Finset.NoncommProd

/-! # Actual self-adjoint subset complement contractions

Finite products use the proved commutation of distinct-site coordinate lifts.
The resulting operator acts on all Hilbert–Schmidt vectors.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace CertificationGaussian
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

private theorem siteLifts_pairwise (A : Finset S)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    (A : Set S).Pairwise (fun s t => Commute (siteCoordinateLift s (L s)) (siteCoordinateLift t (L t))) := by
  intro s _ t _ hst
  exact siteCoordinateLift_commute s t hst (L s) (L t)

def coordinateSubsetLift (A : Finset S)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (S → I) →L[ℂ] EuclideanSpace ℂ (S → I) :=
  A.noncommProd (fun s => siteCoordinateLift s (L s)) (siteLifts_pairwise A L)

theorem coordinateSubsetLift_empty (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    coordinateSubsetLift ∅ L = 1 := Finset.noncommProd_empty _ _

theorem coordinateSubsetLift_insert (A : Finset S) (s : S) (hs : s ∉ A)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    coordinateSubsetLift (insert s A) L = siteCoordinateLift s (L s) * coordinateSubsetLift A L :=
  Finset.noncommProd_insert_of_notMem A s _ _ hs

theorem coordinateSubsetLift_commute (A : Finset S)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) (s : S) (hs : s ∉ A) :
    Commute (siteCoordinateLift s (L s)) (coordinateSubsetLift A L) := by
  apply Finset.noncommProd_commute
  intro t ht
  exact siteCoordinateLift_commute s t (by intro h; subst t; exact hs ht) _ _

theorem coordinateSubsetLift_norm_le_one (A : Finset S)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hL : ∀ s ∈ A, ‖L s‖ ≤ 1) : ‖coordinateSubsetLift A L‖ ≤ 1 := by
  apply Finset.noncommProd_induction A _ _ (fun T => ‖T‖ ≤ 1)
  · intro T U hT hU
    calc
      ‖T * U‖ ≤ ‖T‖ * ‖U‖ := norm_mul_le T U
      _ ≤ 1 * 1 := mul_le_mul hT hU (norm_nonneg U) zero_le_one
      _ = 1 := one_mul 1
  · exact ContinuousLinearMap.norm_id_le
  · intro s hs
    exact (siteCoordinateLift_norm_le s (L s)).trans (hL s hs)

theorem coordinateSubsetLift_adjoint (A : Finset S)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ContinuousLinearMap.adjoint (coordinateSubsetLift A L) =
      coordinateSubsetLift A (fun s => ContinuousLinearMap.adjoint (L s)) := by
  induction A using Finset.induction_on with
  | empty => simp only [coordinateSubsetLift_empty, ContinuousLinearMap.adjoint_one]
  | @insert s A hs ih =>
    rw [coordinateSubsetLift_insert A s hs, coordinateSubsetLift_insert A s hs]
    change ContinuousLinearMap.adjoint ((siteCoordinateLift s (L s)).comp (coordinateSubsetLift A L)) = _
    rw [ContinuousLinearMap.adjoint_comp, siteCoordinateLift_adjoint, ih]
    exact (coordinateSubsetLift_commute A (fun s => ContinuousLinearMap.adjoint (L s)) s hs).eq.symm

theorem coordinateSubsetLift_product (A : Finset S)
    (L : S → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) (v : S → EuclideanSpace ℂ I) :
    coordinateSubsetLift A L (tensorCoordinateVector v) =
      tensorCoordinateVector (fun s => if s ∈ A then L s (v s) else v s) := by
  induction A using Finset.induction_on with
  | empty => simp [coordinateSubsetLift_empty]
  | @insert s A hs ih =>
    rw [coordinateSubsetLift_insert A s hs]
    change siteCoordinateLift s (L s) (coordinateSubsetLift A L (tensorCoordinateVector v)) = _
    rw [ih, siteCoordinateLift_product]
    congr 1
    funext t
    by_cases hts : t = s
    · subst t
      simp [hs]
    · simp [hts]

def matrixTensorCoordinateEquiv : EuclideanSpace ℂ ((S → I) × (S → I)) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (S → I × I) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.arrowProdEquivProdArrow S (fun _ => I) (fun _ => I)).symm

omit [DecidableEq I] in
theorem matrixTensorCoordinateEquiv_tensor (P : S → Matrix I I ℂ) :
    matrixTensorCoordinateEquiv (matrixHilbertSchmidt (wickTensorMatrix P)) =
      tensorCoordinateVector (fun s => matrixHilbertSchmidt (P s)) := rfl

theorem wickTensorMatrix_complement (P : S → Matrix I I ℂ) (ht : ∀ s, (P s).trace = 1)
    (A : Finset S) :
    wickTensorMatrix (fun s => if s ∈ A then
      ((Fintype.card I : ℂ) - 1)⁻¹ • ((P s).trace • 1 - P s) else P s) =
      normalizedProjectorSubset P A := by
  ext x y
  have he (s : S) : (if s ∈ A then
      ((Fintype.card I : ℂ) - 1)⁻¹ • ((P s).trace • 1 - P s) else P s) (x s) (y s) =
      (if s ∈ A then ((Fintype.card I : ℂ) - 1)⁻¹ else 1) *
        (if s ∈ A then 1 - P s else P s) (x s) (y s) := by
    by_cases hs : s ∈ A <;> simp [hs, ht, Matrix.smul_apply, smul_eq_mul]
  simp only [wickTensorMatrix, normalizedProjectorSubset, projectorSubsetFactor, Matrix.smul_apply,
    smul_eq_mul, he]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp [← inv_pow]

/-- The physical subset complement acting on global Hilbert–Schmidt coordinates. -/
def normalizedProjectorSubsetOperator (A : Finset S) :
    EuclideanSpace ℂ ((S → I) × (S → I)) →L[ℂ] EuclideanSpace ℂ ((S → I) × (S → I)) :=
  ((matrixTensorCoordinateEquiv (S := S) (I := I)).symm : _ →L[ℂ] _).comp
    ((coordinateSubsetLift A (fun _ => localComplementHilbert (I := I))).comp
      (matrixTensorCoordinateEquiv (S := S) (I := I) : _ →L[ℂ] _))

theorem normalizedProjectorSubsetOperator_norm_le (hd : 2 ≤ Fintype.card I) (A : Finset S) :
    ‖normalizedProjectorSubsetOperator (I := I) A‖ ≤ 1 := by
  have hn := coordinateSubsetLift_norm_le_one A (fun _ => localComplementHilbert (I := I))
    (fun _ _ => localComplementHilbert_norm_le hd)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖matrixTensorCoordinateEquiv.symm
    (coordinateSubsetLift A (fun _ => localComplementHilbert (I := I))
      (matrixTensorCoordinateEquiv x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h := (coordinateSubsetLift A (fun _ => localComplementHilbert (I := I))).le_opNorm
    (matrixTensorCoordinateEquiv x)
  apply h.trans
  simpa only [LinearIsometryEquiv.norm_map] using mul_le_mul_of_nonneg_right hn
    (norm_nonneg (matrixTensorCoordinateEquiv (S := S) (I := I) x))

theorem normalizedProjectorSubsetOperator_adjoint (A : Finset S) :
    ContinuousLinearMap.adjoint (normalizedProjectorSubsetOperator (I := I) A) =
      normalizedProjectorSubsetOperator A := by
  simp only [normalizedProjectorSubsetOperator, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm,
    coordinateSubsetLift_adjoint, localComplementHilbert_adjoint, ContinuousLinearMap.comp_assoc]

theorem normalizedProjectorSubsetOperator_matrix (A : Finset S) (P : S → Matrix I I ℂ)
    (ht : ∀ s, (P s).trace = 1) :
    normalizedProjectorSubsetOperator A (matrixHilbertSchmidt (wickTensorMatrix P)) =
      matrixHilbertSchmidt (normalizedProjectorSubset P A) := by
  change matrixTensorCoordinateEquiv.symm
    (coordinateSubsetLift A (fun _ => localComplementHilbert (I := I))
      (matrixTensorCoordinateEquiv (matrixHilbertSchmidt (wickTensorMatrix P)))) = _
  rw [matrixTensorCoordinateEquiv_tensor, coordinateSubsetLift_product]
  have he : (fun s => if s ∈ A then localComplementHilbert (matrixHilbertSchmidt (P s))
      else matrixHilbertSchmidt (P s)) =
      (fun s => matrixHilbertSchmidt (if s ∈ A then
        ((Fintype.card I : ℂ) - 1)⁻¹ • ((P s).trace • 1 - P s) else P s)) := by
    funext s
    split_ifs <;> simp only [localComplementHilbert_matrix]
  rw [he, ← matrixTensorCoordinateEquiv_tensor, wickTensorMatrix_complement P ht A,
    LinearIsometryEquiv.symm_apply_apply]

theorem exists_normalizedProjectorSubset_operator (hd : 2 ≤ Fintype.card I) (A : Finset S) :
    ∃ R : EuclideanSpace ℂ ((S → I) × (S → I)) →L[ℂ] EuclideanSpace ℂ ((S → I) × (S → I)),
      ‖R‖ ≤ 1 ∧ ContinuousLinearMap.adjoint R = R ∧
      ∀ (P : S → Matrix I I ℂ), (∀ s, (P s).trace = 1) →
        R (matrixHilbertSchmidt (wickTensorMatrix P)) = matrixHilbertSchmidt (normalizedProjectorSubset P A) :=
  ⟨normalizedProjectorSubsetOperator A, normalizedProjectorSubsetOperator_norm_le hd A,
    normalizedProjectorSubsetOperator_adjoint A, normalizedProjectorSubsetOperator_matrix A⟩

def cardinalityComplementAverage (k : ℕ) :
    EuclideanSpace ℂ ((S → I) × (S → I)) →L[ℂ] EuclideanSpace ℂ ((S → I) × (S → I)) :=
  (((((Fintype.card S).choose k : ℝ)⁻¹ : ℝ) : ℂ)) •
    ∑ A : {A : Finset S // A.card = k}, normalizedProjectorSubsetOperator (I := I) A.val

def cardinalityComplementOperator (J : Finset ℕ) (θ : ℕ → ℝ) :
    EuclideanSpace ℂ ((S → I) × (S → I)) →L[ℂ] EuclideanSpace ℂ ((S → I) × (S → I)) :=
  ∑ k ∈ J, (θ k : ℂ) • cardinalityComplementAverage (S := S) (I := I) k

theorem cardinalityComplementAverage_norm_le (hd : 2 ≤ Fintype.card I) (k : ℕ) :
    ‖cardinalityComplementAverage (S := S) (I := I) k‖ ≤ 1 := by
  have hc : 0 ≤ ((Fintype.card S).choose k : ℝ) := Nat.cast_nonneg _
  have hs : ‖∑ A : {A : Finset S // A.card = k}, normalizedProjectorSubsetOperator (I := I) A.val‖ ≤
      ((Fintype.card S).choose k : ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _ : {A : Finset S // A.card = k}, (1 : ℝ) :=
        Finset.sum_le_sum fun A _ => normalizedProjectorSubsetOperator_norm_le hd A.val
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_finset_len]
  rw [cardinalityComplementAverage, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hc)]
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hc)).trans
  by_cases hzero : ((Fintype.card S).choose k : ℝ) = 0
  · simp [hzero]
  · rw [inv_mul_cancel₀ hzero]

theorem cardinalityComplementOperator_norm_le (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) :
    ‖cardinalityComplementOperator (S := S) (I := I) J θ‖ ≤ ∑ k ∈ J, |θ k| := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (cardinalityComplementAverage_norm_le (S := S) hd k) (abs_nonneg (θ k))

theorem cardinalityComplementAverage_adjoint (k : ℕ) :
    ContinuousLinearMap.adjoint (cardinalityComplementAverage (S := S) (I := I) k) =
      cardinalityComplementAverage k := by
  simp [cardinalityComplementAverage, map_smulₛₗ, map_sum, normalizedProjectorSubsetOperator_adjoint]

theorem cardinalityComplementOperator_adjoint (J : Finset ℕ) (θ : ℕ → ℝ) :
    ContinuousLinearMap.adjoint (cardinalityComplementOperator (S := S) (I := I) J θ) =
      cardinalityComplementOperator J θ := by
  simp [cardinalityComplementOperator, map_smulₛₗ, map_sum, cardinalityComplementAverage_adjoint]
  rfl

theorem cardinalityProjectorKernel_normalized_formula (hd : 2 ≤ Fintype.card I)
    (P : S → Matrix I I ℂ) (J : Finset ℕ) (θ : ℕ → ℝ) :
    cardinalityProjectorKernel P J θ =
      ∑ k ∈ J, ((θ k / ((Fintype.card S).choose k : ℝ) : ℝ) : ℂ) •
        ∑ A : {A : Finset S // A.card = k}, normalizedProjectorSubset P A.val := by
  rw [cardinalityProjectorKernel_formula]
  have hq : ((Fintype.card I - 1 : ℕ) : ℝ) = (Fintype.card I : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [normalizedProjectorSubset, A.property, smul_smul, hq,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
    Complex.ofReal_natCast, Complex.ofReal_one]
  congr 1
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

omit [Fintype I] [DecidableEq I] in
private theorem matrixHilbertSchmidt_sum {K : Type*} (A : K → Matrix I I ℂ) (s : Finset K) :
    matrixHilbertSchmidt (∑ k ∈ s, A k) = ∑ k ∈ s, matrixHilbertSchmidt (A k) := by
  apply PiLp.ext
  intro ij
  simp [matrixHilbertSchmidt, Matrix.sum_apply]

omit [Fintype I] [DecidableEq I] in
private theorem matrixHilbertSchmidt_smul (c : ℂ) (A : Matrix I I ℂ) :
    matrixHilbertSchmidt (c • A) = c • matrixHilbertSchmidt A := rfl

theorem cardinalityComplementOperator_matrix (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (P : S → Matrix I I ℂ) (ht : ∀ s, (P s).trace = 1) :
    cardinalityComplementOperator J θ (matrixHilbertSchmidt (wickTensorMatrix P)) =
      matrixHilbertSchmidt (cardinalityProjectorKernel P J θ) := by
  rw [cardinalityProjectorKernel_normalized_formula hd]
  simp only [cardinalityComplementOperator, cardinalityComplementAverage,
    _root_.sum_apply, _root_.smul_apply,
    normalizedProjectorSubsetOperator_matrix _ P ht,
    matrixHilbertSchmidt_sum, matrixHilbertSchmidt_smul,
    div_eq_mul_inv, Complex.ofReal_inv, Complex.ofReal_mul, smul_smul]

theorem exists_cardinalityProjectorKernel_operator (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) :
    ∃ R : EuclideanSpace ℂ ((S → I) × (S → I)) →L[ℂ] EuclideanSpace ℂ ((S → I) × (S → I)),
      ‖R‖ ≤ ∑ k ∈ J, |θ k| ∧ ContinuousLinearMap.adjoint R = R ∧
      ∀ (P : S → Matrix I I ℂ), (∀ s, (P s).trace = 1) →
        R (matrixHilbertSchmidt (wickTensorMatrix P)) = matrixHilbertSchmidt (cardinalityProjectorKernel P J θ) :=
  ⟨cardinalityComplementOperator J θ, cardinalityComplementOperator_norm_le hd J θ,
    cardinalityComplementOperator_adjoint J θ, cardinalityComplementOperator_matrix hd J θ⟩

theorem normalizedProjectorSubsetOperator_empty :
    normalizedProjectorSubsetOperator (S := S) (I := I) ∅ = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change matrixTensorCoordinateEquiv.symm
    (coordinateSubsetLift ∅ (fun _ : S => localComplementHilbert (I := I))
      (matrixTensorCoordinateEquiv x)) = x
  rw [coordinateSubsetLift_empty]
  exact matrixTensorCoordinateEquiv.symm_apply_apply x

theorem cardinalityComplementAverage_zero :
    cardinalityComplementAverage (S := S) (I := I) 0 = 1 := by
  have he (A : {A : Finset S // A.card = 0}) : A.val = ∅ := Finset.card_eq_zero.mp A.property
  simp only [cardinalityComplementAverage, he, normalizedProjectorSubsetOperator_empty,
    Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
    Nat.choose_zero_right, Nat.cast_one, inv_one, Complex.ofReal_one, one_smul]

theorem cardinalityComplementOperator_zero (θ : ℕ → ℝ) :
    cardinalityComplementOperator (S := S) (I := I) {0} θ = (θ 0 : ℂ) • 1 := by
  simp only [cardinalityComplementOperator, Finset.sum_singleton, cardinalityComplementAverage_zero]

/-- The actual signed map on the real Hilbert space used by Gaussian frames. -/
def cardinalityComplementRealOperator (J : Finset ℕ) (θ : ℕ → ℝ) :
    EuclideanSpace ℂ ((S → I) × (S → I)) →L[ℝ] EuclideanSpace ℂ ((S → I) × (S → I)) :=
  (cardinalityComplementOperator J θ).restrictScalars ℝ

theorem cardinalityComplementRealOperator_norm_le (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) :
    ‖cardinalityComplementRealOperator (S := S) (I := I) J θ‖ ≤ ∑ k ∈ J, |θ k| := by
  simpa only [cardinalityComplementRealOperator, ContinuousLinearMap.norm_restrictScalars] using
    cardinalityComplementOperator_norm_le (S := S) hd J θ

theorem cardinalityComplementRealOperator_adjoint (J : Finset ℕ) (θ : ℕ → ℝ) :
    ContinuousLinearMap.adjoint (cardinalityComplementRealOperator (S := S) (I := I) J θ) =
      cardinalityComplementRealOperator J θ := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hr (a b : EuclideanSpace ℂ ((S → I) × (S → I))) : inner ℝ a b = (inner ℂ a b).re := by
    change (∑ i, (b i * star (a i)).re) = (∑ i, b i * star (a i)).re
    rw [Complex.re_sum]
  rw [hr, hr]
  simp only [cardinalityComplementRealOperator, ContinuousLinearMap.coe_restrictScalars']
  have h := ContinuousLinearMap.adjoint_inner_left
    (cardinalityComplementOperator (S := S) (I := I) J θ) y x
  rw [cardinalityComplementOperator_adjoint] at h
  exact congrArg Complex.re h.symm

theorem cardinalityComplementRealOperator_matrix (hd : 2 ≤ Fintype.card I)
    (J : Finset ℕ) (θ : ℕ → ℝ) (P : S → Matrix I I ℂ) (ht : ∀ s, (P s).trace = 1) :
    cardinalityComplementRealOperator J θ (matrixHilbertSchmidt (wickTensorMatrix P)) =
      matrixHilbertSchmidt (cardinalityProjectorKernel P J θ) := by
  simpa only [cardinalityComplementRealOperator, ContinuousLinearMap.coe_restrictScalars'] using
    cardinalityComplementOperator_matrix hd J θ P ht

end CertificationGaussian
