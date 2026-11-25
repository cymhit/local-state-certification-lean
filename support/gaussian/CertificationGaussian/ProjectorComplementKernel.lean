import CertificationGaussian.TensorReadoutFactorization

/-! # Complement kernels of arbitrary local rank-one effects

These are literal tensor products of arbitrary local projectors. No choice of
orthogonal outcome bases or of unitary coordinates is required.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace CertificationGaussian
variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

def projectorSubsetFactor (P : S → Matrix I I ℂ) (A : Finset S) : Matrix (S → I) (S → I) ℂ :=
  wickTensorMatrix (fun s => if s ∈ A then 1 - P s else P s)

theorem projectorSubsetFactor_mul (P : S → Matrix I I ℂ) (hP : ∀ s, P s * P s = P s)
    (A B : Finset S) :
    projectorSubsetFactor P A * projectorSubsetFactor P B =
      if A = B then projectorSubsetFactor P A else 0 := by
  rw [projectorSubsetFactor, projectorSubsetFactor, wickTensorMatrix_mul]
  have hl (s : S) : (if s ∈ A then 1 - P s else P s) * (if s ∈ B then 1 - P s else P s) =
      if (s ∈ A ↔ s ∈ B) then (if s ∈ A then 1 - P s else P s) else 0 := by
    by_cases ha : s ∈ A <;> by_cases hb : s ∈ B <;> simp [ha, hb, sub_mul, mul_sub, hP s]
  by_cases hab : A = B
  · subst B
    simp only [hl, iff_self, ite_true]
  · simp only [hab, ite_false]
    have hn : ¬∀ s : S, s ∈ A ↔ s ∈ B := fun h => hab (Finset.ext h)
    push Not at hn
    obtain ⟨s, hs⟩ := hn
    have hs' : ¬(s ∈ A ↔ s ∈ B) := by tauto
    ext x y
    change (∏ t : S, ((if t ∈ A then 1 - P t else P t) *
      (if t ∈ B then 1 - P t else P t)) (x t) (y t)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp only [hl, hs', ite_false, Matrix.zero_apply])

theorem projectorSubsetFactor_trace (P : S → Matrix I I ℂ) (ht : ∀ s, (P s).trace = 1)
    (A : Finset S) :
    (projectorSubsetFactor P A).trace = ((Fintype.card I : ℂ) - 1)^A.card := by
  rw [projectorSubsetFactor, wickTensorMatrix_trace]
  simp only [apply_ite Matrix.trace, Matrix.trace_sub, Matrix.trace_one, ht]
  rw [Finset.prod_ite]
  simp

omit [Fintype I] in
theorem projectorSubsetFactor_empty (P : S → Matrix I I ℂ) :
    projectorSubsetFactor P ∅ = wickTensorMatrix P := by simp [projectorSubsetFactor]

/-- Arbitrary signed coefficients over distinct physical complement subsets. -/
def signedProjectorComplementKernel {J : Type*} [Fintype J]
    (P : S → Matrix I I ℂ) (A : J → Finset S) (c : J → ℝ) : Matrix (S → I) (S → I) ℂ :=
  ∑ j, (c j : ℂ) • projectorSubsetFactor P (A j)

theorem signedProjectorComplementKernel_square {J : Type*} [Fintype J]
    (P : S → Matrix I I ℂ) (hP : ∀ s, P s * P s = P s)
    (A : J → Finset S) (hA : Function.Injective A) (c : J → ℝ) :
    (signedProjectorComplementKernel P A c)^2 =
      signedProjectorComplementKernel P A (fun j => (c j)^2) := by
  classical
  simp only [pow_two, signedProjectorComplementKernel, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, projectorSubsetFactor_mul P hP, hA.eq_iff,
    smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Complex.ofReal_mul]

theorem signedProjectorComplementKernel_trace {J : Type*} [Fintype J]
    (P : S → Matrix I I ℂ) (ht : ∀ s, (P s).trace = 1)
    (A : J → Finset S) (c : J → ℝ) :
    (signedProjectorComplementKernel P A c).trace =
      ∑ j, (c j : ℂ) * ((Fintype.card I : ℂ) - 1)^(A j).card := by
  simp only [signedProjectorComplementKernel, Matrix.trace_sum, Matrix.trace_smul,
    projectorSubsetFactor_trace P ht, smul_eq_mul]

theorem signedProjectorComplementKernel_trace_square {J : Type*} [Fintype J]
    (P : S → Matrix I I ℂ) (hP : ∀ s, P s * P s = P s) (ht : ∀ s, (P s).trace = 1)
    (A : J → Finset S) (hA : Function.Injective A) (c : J → ℝ) :
    ((signedProjectorComplementKernel P A c)^2).trace =
      ∑ j, ((c j)^2 : ℂ) * ((Fintype.card I : ℂ) - 1)^(A j).card := by
  rw [signedProjectorComplementKernel_square P hP A hA, signedProjectorComplementKernel_trace P ht]
  simp only [Complex.ofReal_pow]

omit [Fintype I] in
theorem projectorSubsetFactor_hermitian (P : S → Matrix I I ℂ)
    (hH : ∀ s, (P s).IsHermitian) (A : Finset S) : (projectorSubsetFactor P A).IsHermitian := by
  change (projectorSubsetFactor P A).conjTranspose = _
  ext x y
  simp only [projectorSubsetFactor, wickTensorMatrix, Matrix.conjTranspose_apply, star_prod]
  apply Finset.prod_congr rfl
  intro s _
  have hs : (if s ∈ A then 1 - P s else P s).IsHermitian := by
    split_ifs
    · exact Matrix.isHermitian_one.sub (hH s)
    · exact hH s
  exact congrArg (fun B : Matrix I I ℂ => B (x s) (y s)) hs.eq

omit [Fintype I] in
theorem signedProjectorComplementKernel_hermitian {J : Type*} [Fintype J]
    (P : S → Matrix I I ℂ) (hH : ∀ s, (P s).IsHermitian)
    (A : J → Finset S) (c : J → ℝ) : (signedProjectorComplementKernel P A c).IsHermitian := by
  unfold signedProjectorComplementKernel Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact ((projectorSubsetFactor_hermitian P hH (A j)).smul
    (show IsSelfAdjoint (c j : ℂ) from by simp [IsSelfAdjoint])).eq

/-- The literal normalized complementary product for one subset. -/
def normalizedProjectorSubset (P : S → Matrix I I ℂ) (A : Finset S) : Matrix (S → I) (S → I) ℂ :=
  ((((Fintype.card I : ℝ) - 1)^A.card)⁻¹ : ℂ) • projectorSubsetFactor P A

theorem normalizedProjectorSubset_empty (P : S → Matrix I I ℂ) :
    normalizedProjectorSubset P ∅ = wickTensorMatrix P := by
  simp [normalizedProjectorSubset, projectorSubsetFactor_empty]

theorem normalizedProjectorSubset_trace (P : S → Matrix I I ℂ)
    (ht : ∀ s, (P s).trace = 1) (hd : 2 ≤ Fintype.card I) (A : Finset S) :
    (normalizedProjectorSubset P A).trace = 1 := by
  have hd0 : (Fintype.card I : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (by omega : Fintype.card I ≠ 1)
  rw [normalizedProjectorSubset, Matrix.trace_smul, projectorSubsetFactor_trace P ht]
  simp only [Complex.ofReal_natCast, smul_eq_mul]
  exact inv_mul_cancel₀ (pow_ne_zero _ hd0)

theorem normalizedProjectorSubset_trace_square (P : S → Matrix I I ℂ)
    (hP : ∀ s, P s * P s = P s) (ht : ∀ s, (P s).trace = 1)
    (hd : 2 ≤ Fintype.card I) (A : Finset S) :
    ((normalizedProjectorSubset P A)^2).trace =
      ((((Fintype.card I : ℝ) - 1)^A.card)⁻¹ : ℂ) := by
  have hd0 : (Fintype.card I : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (by omega : Fintype.card I ≠ 1)
  simp only [normalizedProjectorSubset, pow_two, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, projectorSubsetFactor_mul P hP, ite_true, Matrix.trace_smul,
    projectorSubsetFactor_trace P ht, Complex.ofReal_natCast, smul_eq_mul]
  field_simp

end CertificationGaussian
