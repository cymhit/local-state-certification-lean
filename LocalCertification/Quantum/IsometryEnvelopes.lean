import LocalCertification.Quantum.StateTraceBounds

set_option autoImplicit false
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
namespace LocalCertification.Quantum
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The orthogonal complement of the range of a genuine rectangular isometry is positive. -/
theorem isometry_range_complement_pos (Q : Matrix I J ℂ) (hQ : Qᴴ*Q=1) :
    (1-Q*Qᴴ).PosSemidef := by
  have hp : (Q*Qᴴ)*(Q*Qᴴ)=Q*Qᴴ := by
    calc
      _ = Q*(Qᴴ*Q)*Qᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ,Matrix.mul_one]
  have he : (1-Q*Qᴴ)ᴴ*(1-Q*Qᴴ) = 1-Q*Qᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    noncomm_ring [hp]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype I] [DecidableEq I] in
/-- A selected diagonal rank-one projection is the actual outer product of the corresponding column. -/
theorem isometry_selected_column (Q : Matrix I J ℂ) (i : J) :
    Q * Matrix.single i i (1:ℂ) * Qᴴ = Matrix.vecMulVec (fun x => Q x i) (star (fun x => Q x i)) := by
  ext a b
  change ∑ j, (Q*Matrix.single i i (1:ℂ)) a j * star (Q b j) = Q a i * star (Q b i)
  rw [Finset.sum_eq_single i]
  · rw [Matrix.mul_single_apply_same]
    simp
  · intro j _ hji
    rw [Matrix.mul_single_apply_of_ne (1:ℂ) i i a j hji Q]
    simp
  · simp

omit [Fintype J] in
private theorem diagonal_two_levels (i : J) (c : ℝ) :
    Matrix.diagonal (fun j : J => if j=i then (1:ℂ) else (c:ℂ)) =
      (1-c) • Matrix.single i i (1:ℂ)+c • (1 : Matrix J J ℂ) := by
  ext a b
  by_cases hab : a=b
  · subst b
    by_cases hai : a=i
    · subst a
      simp [Matrix.single]
    · have hia : i≠a := Ne.symm hai
      simp [Matrix.single,hai,hia]
  · have hni : ¬(i=a ∧ i=b) := by
      rintro ⟨ha,hb⟩
      exact hab (ha.symm.trans hb)
    simp [Matrix.single,hab,hni]

omit [Fintype I] [DecidableEq I] in
private theorem conjugate_two_levels (Q : Matrix I J ℂ) (i : J) (c : ℝ) :
    Q * Matrix.diagonal (fun j : J => if j=i then (1:ℂ) else (c:ℂ)) * Qᴴ =
      (1-c) • (Q*Matrix.single i i (1:ℂ)*Qᴴ)+c • (Q*Qᴴ) := by
  rw [diagonal_two_levels]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]

/-- All remaining spectral coefficients in [l,u] and the zero spectrum off the isometry range
produce exact Loewner envelopes around the selected unit column. -/
theorem isometry_diagonal_envelopes (Q : Matrix I J ℂ) (hQ : Qᴴ*Q=1)
    (i : J) (c : J → ℝ) (hc : c i=1) (l u : ℝ) (hl0 : l≤0) (hu0 : 0≤u)
    (hcl : ∀ j, j≠i → l≤c j) (hcu : ∀ j, j≠i → c j≤u) :
    Q*Matrix.single i i (1:ℂ)*Qᴴ + l • (1-Q*Matrix.single i i (1:ℂ)*Qᴴ) ≤
      Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ ∧
    Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ ≤
      Q*Matrix.single i i (1:ℂ)*Qᴴ + u • (1-Q*Matrix.single i i (1:ℂ)*Qᴴ) := by
  have hdiagL : (Matrix.diagonal (fun j => (c j:ℂ))-
      Matrix.diagonal (fun j => if j=i then (1:ℂ) else (l:ℂ))).PosSemidef := by
    rw [Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases hji : j=i
    · simp [hji,hc]
    · simpa [hji,Complex.nonneg_iff] using hcl j hji
  have hdiagU : (Matrix.diagonal (fun j => if j=i then (1:ℂ) else (u:ℂ))-
      Matrix.diagonal (fun j => (c j:ℂ))).PosSemidef := by
    rw [Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases hji : j=i
    · simp [hji,hc]
    · simpa [hji,Complex.nonneg_iff] using hcu j hji
  have hL := (hdiagL.mul_mul_conjTranspose_same Q).add
    ((isometry_range_complement_pos Q hQ).smul (neg_nonneg.mpr hl0))
  have hU := (hdiagU.mul_mul_conjTranspose_same Q).add
    ((isometry_range_complement_pos Q hQ).smul hu0)
  simp only [Matrix.mul_sub,Matrix.sub_mul,conjugate_two_levels] at hL hU
  constructor
  · apply Matrix.le_iff.mpr
    convert hL using 1
    simp only [sub_smul,one_smul,smul_sub,neg_smul]
    abel
  · apply Matrix.le_iff.mpr
    convert hU using 1
    simp only [sub_smul,one_smul,smul_sub]
    abel

end LocalCertification.Quantum
