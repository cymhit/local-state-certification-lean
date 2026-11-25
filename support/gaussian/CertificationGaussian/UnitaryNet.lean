import CertificationGaussian.GaussianRotation
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open scoped BigOperators
open Classical
namespace CertificationGaussian

/-- Finite code for the closed interval [-1,1], with positive mesh. -/
def intervalCode (δ : ℝ) (hδ : 0 < δ) (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    Fin (Nat.ceil (2/δ)+1) :=
  ⟨Nat.floor ((x+1)/δ), by
    have h : (x+1)/δ ≤ (Nat.ceil (2/δ):ℝ) :=
      (div_le_div_of_nonneg_right (by linarith) hδ.le).trans (Nat.le_ceil _)
    have h' := Nat.floor_le_of_le h
    omega⟩

theorem intervalCode_same_close {δ : ℝ} (hδ : 0 < δ) {x y : ℝ}
    (hx : -1 ≤ x ∧ x ≤ 1) (hy : -1 ≤ y ∧ y ≤ 1)
    (h : intervalCode δ hδ x hx = intervalCode δ hδ y hy) : |x-y| < δ := by
  have hcode : Nat.floor ((x+1)/δ) = Nat.floor ((y+1)/δ) := congrArg Fin.val h
  have hxlo := Nat.floor_le (show 0 ≤ (x+1)/δ from div_nonneg (by linarith [hx.1]) hδ.le)
  have hylo := Nat.floor_le (show 0 ≤ (y+1)/δ from div_nonneg (by linarith [hy.1]) hδ.le)
  have hxhi := Nat.lt_floor_add_one ((x+1)/δ)
  have hyhi := Nat.lt_floor_add_one ((y+1)/δ)
  rw [hcode] at hxlo hxhi
  simp only [add_div] at hxlo hxhi hylo hyhi
  have hxy : (x-y)/δ < 1 := by rw [sub_div]; linarith
  have hyx : (y-x)/δ < 1 := by rw [sub_div]; linarith
  have hxy' := (div_lt_iff₀ hδ).mp hxy
  have hyx' := (div_lt_iff₀ hδ).mp hyx
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

abbrev LocalUnitary (d : Nat) := ↥(unitary (Matrix (Fin d) (Fin d) ℂ))

def unitaryRealCoordinate {d : Nat} (U : LocalUnitary d) (a : Fin 2 × Fin d × Fin d) : ℝ :=
  if a.1 = 0 then (U.1 a.2.1 a.2.2).re else (U.1 a.2.1 a.2.2).im

theorem unitaryRealCoordinate_bound {d : Nat} (U : LocalUnitary d) (a : Fin 2 × Fin d × Fin d) :
    -1 ≤ unitaryRealCoordinate U a ∧ unitaryRealCoordinate U a ≤ 1 := by
  have h := entry_norm_bound_of_unitary U.2 a.2.1 a.2.2
  unfold unitaryRealCoordinate
  split_ifs
  · exact abs_le.mp ((Complex.abs_re_le_norm _).trans h)
  · exact abs_le.mp ((Complex.abs_im_le_norm _).trans h)

def unitaryCode (d : Nat) (δ : ℝ) (hδ : 0 < δ) (U : LocalUnitary d) :
    (Fin 2 × Fin d × Fin d) → Fin (Nat.ceil (2/δ)+1) :=
  fun a => intervalCode δ hδ (unitaryRealCoordinate U a) (unitaryRealCoordinate_bound U a)

/-- Every occupied cell contributes an actual unitary; empty cells use the identity. -/
def unitaryCodeRepresentative (d : Nat) (δ : ℝ) (hδ : 0 < δ)
    (c : (Fin 2 × Fin d × Fin d) → Fin (Nat.ceil (2/δ)+1)) : LocalUnitary d :=
  if h : ∃ U, unitaryCode d δ hδ U = c then Classical.choose h else 1

def unitaryCoordinateNet (d : Nat) (δ : ℝ) (hδ : 0 < δ) : Finset (LocalUnitary d) :=
  Finset.univ.image (unitaryCodeRepresentative d δ hδ)

theorem unitaryCoordinateNet_card (d : Nat) {δ : ℝ} (hδ : 0 < δ) :
    (unitaryCoordinateNet d δ hδ).card ≤ (Nat.ceil (2/δ)+1)^(2*d^2) := by
  have h := Finset.card_image_le (f := unitaryCodeRepresentative d δ hδ) (s := Finset.univ)
  simpa [unitaryCoordinateNet, Fintype.card_fun, pow_two, mul_assoc] using h

/-- The finite net covers every unitary in each real and imaginary matrix coordinate. -/
theorem unitaryCoordinateNet_covers (d : Nat) {δ : ℝ} (hδ : 0 < δ) (U : LocalUnitary d) :
    ∃ V ∈ unitaryCoordinateNet d δ hδ,
      ∀ a, |unitaryRealCoordinate U a - unitaryRealCoordinate V a| < δ := by
  let c := unitaryCode d δ hδ U
  let V := unitaryCodeRepresentative d δ hδ c
  have hc : ∃ W, unitaryCode d δ hδ W = c := ⟨U, rfl⟩
  have hV : unitaryCode d δ hδ V = c := by
    simpa only [V, unitaryCodeRepresentative, dite_eq_left hc] using Classical.choose_spec hc
  refine ⟨V, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
  intro a
  apply intervalCode_same_close hδ (unitaryRealCoordinate_bound U a) (unitaryRealCoordinate_bound V a)
  exact congrFun hV.symm a

/-- Coordinate closeness gives the explicit squared Frobenius error, without any norm-instance ambiguity. -/
theorem unitaryCoordinateNet_covers_sq (d : Nat) {δ : ℝ} (hδ : 0 < δ) (U : LocalUnitary d) :
    ∃ V ∈ unitaryCoordinateNet d δ hδ,
      ∑ i, ∑ j, ‖U.1 i j - V.1 i j‖^2 ≤ 2*(d:ℝ)^2*δ^2 := by
  obtain ⟨V, hV, hclose⟩ := unitaryCoordinateNet_covers d hδ U
  refine ⟨V, hV, ?_⟩
  have hentry (i j : Fin d) : ‖U.1 i j - V.1 i j‖^2 ≤ 2*δ^2 := by
    have hre : |(U.1 i j - V.1 i j).re| ≤ δ := by
      simpa [unitaryRealCoordinate] using (hclose (0,i,j)).le
    have him : |(U.1 i j - V.1 i j).im| ≤ δ := by
      simpa [unitaryRealCoordinate] using (hclose (1,i,j)).le
    have hr := (sq_le_sq₀ (abs_nonneg _) hδ.le).mpr hre
    have hi := (sq_le_sq₀ (abs_nonneg _) hδ.le).mpr him
    simp only [sq_abs] at hr hi
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, 2*δ^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
    _ = _ := by simp; ring

open scoped Matrix.Norms.Frobenius in
/-- The actual Euclidean operator norm is bounded by the explicit Frobenius square sum. -/
theorem matrix_operator_norm_le_entry_sqrt {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) :
    ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) := by
  have hnorm : ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) := by
    rw [Matrix.frobenius_norm_def]
    simp only [Real.rpow_two, Real.sqrt_eq_rpow]
  rw [← hnorm]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  have he : A * Matrix.replicateCol Unit (WithLp.ofLp x) =
      Matrix.replicateCol Unit (WithLp.ofLp (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A x)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h := Matrix.frobenius_norm_mul A (Matrix.replicateCol Unit (WithLp.ofLp x))
  rw [he, Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol] at h
  exact h

/-- A genuine finite unitary epsilon-net; the mesh is epsilon/(2d). -/
def unitaryNet (d : Nat) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) : Finset (LocalUnitary d) :=
  unitaryCoordinateNet d (ε/(2*d)) (by positivity)

theorem unitaryNet_covers_sq {d : Nat} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (U : LocalUnitary d) :
    ∃ V ∈ unitaryNet d hd ε hε,
      ∑ i, ∑ j, ‖U.1 i j - V.1 i j‖^2 ≤ ε^2 := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0<d by omega)
  obtain ⟨V, hV, he⟩ := unitaryCoordinateNet_covers_sq d (show 0 < ε/(2*d) by positivity) U
  refine ⟨V, hV, he.trans ?_⟩
  have h : 2*(d:ℝ)^2*(ε/(2*d))^2 = ε^2/2 := by field_simp
  rw [h]
  nlinarith [sq_nonneg ε]

theorem unitaryNet_covers_operator {d : Nat} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (U : LocalUnitary d) :
    ∃ V ∈ unitaryNet d hd ε hε,
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (U.1-V.1)‖ ≤ ε := by
  obtain ⟨V, hV, he⟩ := unitaryNet_covers_sq hd hε U
  refine ⟨V, hV, (matrix_operator_norm_le_entry_sqrt _).trans ?_⟩
  exact (Real.sqrt_le_sqrt he).trans_eq (Real.sqrt_sq hε.le)

theorem unitaryNet_card {d : Nat} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ((unitaryNet d hd ε hε).card:ℝ) ≤ (2+4*d/ε)^(2*d^2) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0<d by omega)
  have hcard := unitaryCoordinateNet_card d (show 0 < ε/(2*d) by positivity)
  have hb : (Nat.ceil (2/(ε/(2*d)))+1:ℝ) ≤ 2+4*d/ε := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2/(ε/(2*d)) by positivity)
    have he : 2/(ε/(2*d)) = 4*d/ε := by field_simp; norm_num
    rw [he] at h ⊢
    linarith
  have hcardR : ((unitaryCoordinateNet d (ε/(2*d)) (by positivity)).card:ℝ) ≤
      ((Nat.ceil (2/(ε/(2*d)))+1)^(2*d^2):Nat) := Nat.cast_le.mpr hcard
  have hcardR' : ((unitaryNet d hd ε hε).card:ℝ) ≤ (Nat.ceil (2/(ε/(2*d)))+1:ℝ)^(2*d^2) := by
    simpa only [unitaryNet, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hcardR
  exact hcardR'.trans (pow_le_pow_left₀ (by positivity) hb _)

end CertificationGaussian
