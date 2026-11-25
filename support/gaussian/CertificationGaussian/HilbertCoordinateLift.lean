import CertificationGaussian.LocalComplementHilbert

/-! # Actual coordinate lifts of local Hilbert operators

The norm estimate uses finite squared-norm slicing. This is a tensor action on
all vectors, not a bound restricted to pure product vectors.
-/

noncomputable section
open scoped BigOperators
namespace CertificationGaussian
variable {I J : Type*} [Fintype I] [Fintype J]

def euclideanSlice (x : EuclideanSpace ℂ (I × J)) (j : J) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i => x (i, j))

omit [Fintype I] [Fintype J] in
theorem euclideanSlice_continuous (j : J) :
    Continuous (fun x : EuclideanSpace ℂ (I × J) => euclideanSlice x j) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => PiLp.continuous_apply 2 _ (i, j))

def coordinateLift (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × J) →L[ℂ] EuclideanSpace ℂ (I × J) where
  toFun x := WithLp.toLp 2 (fun ij => L (euclideanSlice x ij.2) ij.1)
  map_add' x y := by
    apply PiLp.ext
    intro ij
    change L (euclideanSlice x ij.2 + euclideanSlice y ij.2) ij.1 = _
    rw [map_add]
    rfl
  map_smul' c x := by
    apply PiLp.ext
    intro ij
    change L (c • euclideanSlice x ij.2) ij.1 = _
    rw [map_smul]
    rfl
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun ij =>
    (PiLp.continuous_apply 2 _ ij.1).comp (L.continuous.comp (euclideanSlice_continuous ij.2)))

omit [Fintype I] [Fintype J] in
theorem coordinateLift_apply (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × J)) (i : I) (j : J) :
    coordinateLift L x (i, j) = L (euclideanSlice x j) i := rfl

omit [Fintype I] [Fintype J] in
theorem coordinateLift_slice (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × J)) (j : J) :
    euclideanSlice (coordinateLift L x) j = L (euclideanSlice x j) := rfl

theorem euclideanSlice_norm_sq_sum (x : EuclideanSpace ℂ (I × J)) :
    (∑ j, ‖euclideanSlice x j‖^2) = ‖x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, euclideanSlice,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem coordinateLift_norm_sq_le (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × J)) :
    ‖coordinateLift L x‖^2 ≤ ‖L‖^2 * ‖x‖^2 := by
  rw [← euclideanSlice_norm_sq_sum, ← euclideanSlice_norm_sq_sum x]
  simp only [coordinateLift_slice]
  calc
    _ ≤ ∑ j, ‖L‖^2 * ‖euclideanSlice x j‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm (euclideanSlice x j)) 2
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem coordinateLift_norm_apply_le (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (I × J)) :
    ‖WithLp.toLp 2 (fun ij : I × J => L (WithLp.toLp 2 (fun i => x (i, ij.2))) ij.1)‖ ≤
      ‖L‖ * ‖x‖ := by
  change ‖coordinateLift L x‖ ≤ ‖L‖ * ‖x‖
  have hs := coordinateLift_norm_sq_le L x
  have hp := mul_nonneg (norm_nonneg L) (norm_nonneg x)
  nlinarith [norm_nonneg (coordinateLift L x)]

theorem coordinateLift_norm_le (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ‖coordinateLift (J := J) L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact coordinateLift_norm_apply_le L

theorem euclideanSlice_inner_sum (x y : EuclideanSpace ℂ (I × J)) :
    inner ℂ x y = ∑ j, inner ℂ (euclideanSlice x j) (euclideanSlice y j) := by
  change (∑ ij : I × J, y ij * star (x ij)) = ∑ j, ∑ i, y (i, j) * star (x (i, j))
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem coordinateLift_adjoint (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ContinuousLinearMap.adjoint (coordinateLift (J := J) L) =
      coordinateLift (ContinuousLinearMap.adjoint L) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, euclideanSlice_inner_sum, euclideanSlice_inner_sum]
  simp only [coordinateLift_slice, ContinuousLinearMap.adjoint_inner_left]

omit [Fintype I] [Fintype J] in
theorem coordinateLift_product (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (v : EuclideanSpace ℂ I) (w : EuclideanSpace ℂ J) :
    coordinateLift L (WithLp.toLp 2 (fun ij : I × J => v ij.1 * w ij.2)) =
      WithLp.toLp 2 (fun ij : I × J => L v ij.1 * w ij.2) := by
  apply PiLp.ext
  intro ij
  have hs : euclideanSlice (WithLp.toLp 2 (fun ij : I × J => v ij.1 * w ij.2)) ij.2 =
      w ij.2 • v := by
    apply PiLp.ext
    intro i
    simp [euclideanSlice, mul_comm]
  rw [coordinateLift_apply, hs, map_smul]
  simp [mul_comm]

omit [Fintype I] [Fintype J] in
theorem coordinateLift_id :
    coordinateLift (J := J) (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ I)) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (I × J)) := rfl

omit [Fintype I] [Fintype J] in
theorem coordinateLift_comp (L M : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    coordinateLift (J := J) (L.comp M) = (coordinateLift L).comp (coordinateLift M) := rfl

section Sites
variable {S : Type*} [Fintype S] [DecidableEq S]

def siteCoordinateEquiv (s : S) : EuclideanSpace ℂ (S → I) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (I × ({t : S // t ≠ s} → I)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.funSplitAt s I)

def siteCoordinateLift (s : S) (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (S → I) →L[ℂ] EuclideanSpace ℂ (S → I) :=
  ((siteCoordinateEquiv (I := I) s).symm : _ →L[ℂ] _).comp
    ((coordinateLift (J := {t : S // t ≠ s} → I) L).comp
      (siteCoordinateEquiv (I := I) s : _ →L[ℂ] _))

theorem siteCoordinateLift_apply [DecidableEq I] (s : S)
    (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (S → I)) (a : S → I) :
    siteCoordinateLift s L x a = L (WithLp.toLp 2 (fun i => x (Function.update a s i))) (a s) := by
  have he (i : I) : (Equiv.funSplitAt s I).symm (i, fun t => a t) = Function.update a s i := by
    funext t
    by_cases ht : t = s
    · subst t
      simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Equiv.funSplitAt, Equiv.piSplitAt, ht]
  simp only [siteCoordinateLift, ContinuousLinearMap.comp_apply, siteCoordinateEquiv,
    LinearIsometryEquiv.piLpCongrLeft_symm]
  change L (WithLp.toLp 2 (fun i => x ((Equiv.funSplitAt s I).symm (i, fun t => a t)))) (a s) = _
  simp_rw [he]

theorem siteCoordinateLift_norm_apply_le (s : S)
    (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) (x : EuclideanSpace ℂ (S → I)) :
    ‖siteCoordinateLift s L x‖ ≤ ‖L‖ * ‖x‖ := by
  change ‖(siteCoordinateEquiv s).symm (coordinateLift L (siteCoordinateEquiv s x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h := coordinateLift_norm_apply_le L (siteCoordinateEquiv s x)
  change ‖coordinateLift L (siteCoordinateEquiv s x)‖ ≤ ‖L‖ * ‖siteCoordinateEquiv s x‖ at h
  simpa only [LinearIsometryEquiv.norm_map] using h

theorem siteCoordinateLift_norm_le (s : S)
    (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) : ‖siteCoordinateLift s L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact siteCoordinateLift_norm_apply_le s L

theorem siteCoordinateLift_adjoint (s : S)
    (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ContinuousLinearMap.adjoint (siteCoordinateLift s L) =
      siteCoordinateLift s (ContinuousLinearMap.adjoint L) := by
  simp only [siteCoordinateLift, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm, coordinateLift_adjoint,
    ContinuousLinearMap.comp_assoc]

theorem siteCoordinateLift_id (s : S) :
    siteCoordinateLift s (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ I)) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (S → I)) := by
  apply ContinuousLinearMap.ext
  intro x
  change (siteCoordinateEquiv s).symm (siteCoordinateEquiv s x) = x
  exact (siteCoordinateEquiv s).symm_apply_apply x

theorem siteCoordinateLift_comp (s : S) (L M : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    siteCoordinateLift s (L.comp M) = (siteCoordinateLift s L).comp (siteCoordinateLift s M) := by
  apply ContinuousLinearMap.ext
  intro x
  change (siteCoordinateEquiv s).symm (coordinateLift L (coordinateLift M (siteCoordinateEquiv s x))) =
    (siteCoordinateEquiv s).symm (coordinateLift L (siteCoordinateEquiv s
      ((siteCoordinateEquiv s).symm (coordinateLift M (siteCoordinateEquiv s x)))))
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem euclideanOperator_expansion [DecidableEq I]
    (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) (x : EuclideanSpace ℂ I) (i : I) :
    L x i = ∑ j, x j * L (WithLp.toLp 2 (Pi.single j 1)) i := by
  have hx : x = ∑ j, x j • (WithLp.toLp 2 (Pi.single j 1) : EuclideanSpace ℂ I) := by
    apply PiLp.ext
    intro k
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp

theorem siteCoordinateLift_expansion [DecidableEq I] (s : S)
    (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (x : EuclideanSpace ℂ (S → I)) (a : S → I) :
    siteCoordinateLift s L x a =
      ∑ i, x (Function.update a s i) * L (WithLp.toLp 2 (Pi.single i 1)) (a s) := by
  rw [siteCoordinateLift_apply, euclideanOperator_expansion]

theorem siteCoordinateLift_commute [DecidableEq I] (s t : S) (hst : s ≠ t)
    (L M : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    (siteCoordinateLift s L).comp (siteCoordinateLift t M) =
      (siteCoordinateLift t M).comp (siteCoordinateLift s L) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, siteCoordinateLift_expansion,
    Function.update_of_ne hst, Function.update_of_ne hst.symm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Function.update_comm hst]
  ring

def tensorCoordinateVector (v : S → EuclideanSpace ℂ I) : EuclideanSpace ℂ (S → I) :=
  WithLp.toLp 2 (fun a => ∏ s, v s (a s))

theorem siteCoordinateLift_product [DecidableEq I] (s : S)
    (L : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) (v : S → EuclideanSpace ℂ I) :
    siteCoordinateLift s L (tensorCoordinateVector v) =
      tensorCoordinateVector (Function.update v s (L (v s))) := by
  apply PiLp.ext
  intro a
  let c : ℂ := ∏ t ∈ Finset.univ.erase s, v t (a t)
  have hslice : (WithLp.toLp 2 (fun i => tensorCoordinateVector v (Function.update a s i)) :
      EuclideanSpace ℂ I) = c • v s := by
    apply PiLp.ext
    intro i
    change (∏ t, v t (Function.update a s i t)) = c * v s i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s), Function.update_self]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro t ht
    rw [Function.update_of_ne (Finset.mem_erase.mp ht).1]
  rw [siteCoordinateLift_apply, hslice, map_smul]
  change c * L (v s) (a s) = ∏ t, Function.update v s (L (v s)) t (a t)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s), Function.update_self, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro t ht
  rw [Function.update_of_ne (Finset.mem_erase.mp ht).1]

end Sites
end CertificationGaussian
