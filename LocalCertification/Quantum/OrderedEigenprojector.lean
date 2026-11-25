import LocalCertification.Quantum.MeasurableEigenvalues
import Mathlib.Analysis.Matrix.Normed

/-! # Measurable eigenspace projections

In eigenvalue coordinates the projection is the indicator of equality to
the selected eigenvalue. In the original coordinates it is a polynomial
in the matrix on each multiplicity stratum.
-/

set_option autoImplicit false
open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace LocalCertification.Quantum
variable {I J : Type*} [Fintype I] [DecidableEq I]

private def matrixFilter (A : Matrix I I ℂ) (t : ℝ) (e : J → ℝ) :
    List J → Matrix I I ℂ
  | [] => 1
  | k :: ks => if t = e k then matrixFilter A t e ks else
      (((t - e k : ℝ) : ℂ)⁻¹ • (A - (e k : ℂ) • 1)) * matrixFilter A t e ks

private def valueFilter (x t : ℝ) (e : J → ℝ) : List J → ℂ
  | [] => 1
  | k :: ks => if t = e k then valueFilter x t e ks else
      (((t - e k : ℝ) : ℂ)⁻¹ * ((x - e k : ℝ) : ℂ)) * valueFilter x t e ks

private theorem valueFilter_self (t : ℝ) (e : J → ℝ) (ks : List J) :
    valueFilter t t e ks = 1 := by
  induction ks with
  | nil => rfl
  | cons i ks ih =>
    by_cases hi : t = e i
    · simp only [valueFilter, ite_eq_left hi, ih]
    · have h : ((t - e i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hi
      simp only [valueFilter, ite_eq_right hi, ih, inv_mul_cancel₀ h, mul_one]

private theorem valueFilter_zero (x t : ℝ) (hx : x ≠ t) (e : J → ℝ)
    (ks : List J) (hmem : ∃ i ∈ ks, e i = x) : valueFilter x t e ks = 0 := by
  induction ks with
  | nil => simp at hmem
  | cons j ks ih =>
    by_cases hj : e j = x
    · simp [valueFilter, hj, Ne.symm hx]
    · have hm : ∃ i ∈ ks, e i = x := by
        obtain ⟨i, hi, he⟩ := hmem
        rcases List.mem_cons.mp hi with h | h
        · exact (hj (h ▸ he)).elim
        · exact ⟨i, h, he⟩
      simp [valueFilter, ih hm]

/-- The projection onto the full eigenspace of the ordered eigenvalue at i. -/
def orderedEigenprojector {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card I)) : Matrix I I ℂ :=
  matrixFilter A (hA.eigenvalues₀ i) hA.eigenvalues₀ (List.finRange _)

private theorem measurable_matrixFilter {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix I I ℂ) (hA : Measurable A) (t : Ω → ℝ) (ht : Measurable t)
    (e : Ω → J → ℝ) (he : ∀ j, Measurable fun s => e s j) (ks : List J) :
    Measurable fun s => matrixFilter (A s) (t s) (e s) ks := by
  induction ks with
  | nil => exact measurable_const
  | cons j ks ih =>
    simp only [matrixFilter]
    apply Measurable.ite (measurableSet_eq_fun ht (he j)) ih
    apply Measurable.of_eval_matrix
    intro p q
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    fun_prop (disch := first | exact ht | exact he _ | exact hA.eval_matrix | exact ih.eval_matrix)

theorem measurable_orderedEigenprojector {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix I I ℂ) (hA : Measurable A) (hself : ∀ s, (A s).IsHermitian)
    (i : Fin (Fintype.card I)) : Measurable fun s => orderedEigenprojector (hself s) i := by
  have h := measurable_ordered_eigenvalues A hA hself
  exact measurable_matrixFilter A hA _ ((measurable_pi_apply i).comp h) _
    (fun k => (measurable_pi_apply k).comp h) _

private theorem matrixFilter_mulVec (A : Matrix I I ℂ) (v : I → ℂ)
    (x t : ℝ) (hv : A *ᵥ v = (x : ℂ) • v) (e : J → ℝ) (ks : List J) :
    matrixFilter A t e ks *ᵥ v = valueFilter x t e ks • v := by
  induction ks with
  | nil => simp [matrixFilter, valueFilter]
  | cons k ks ih =>
    by_cases ht : t = e k
    · simpa only [matrixFilter, valueFilter, ite_eq_left ht] using ih
    · simp only [matrixFilter, valueFilter, ite_eq_right ht, ← mulVec_mulVec, ih, Matrix.mulVec_smul,
        Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv,
        ← sub_smul, ← mul_smul, Complex.ofReal_sub]
      congr 1
      ring

theorem orderedEigenprojector_mulVec {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card I)) (j : I) :
    orderedEigenprojector hA i *ᵥ ⇑(hA.eigenvectorBasis j) =
      if hA.eigenvalues j = hA.eigenvalues₀ i then ⇑(hA.eigenvectorBasis j) else 0 := by
  have hv := hA.mulVec_eigenvectorBasis j
  rw [orderedEigenprojector, matrixFilter_mulVec _ _ (hA.eigenvalues j) _ (by simpa using hv)]
  split_ifs with hj
  · rw [hj, valueFilter_self, one_smul]
  · rw [valueFilter_zero _ _ hj, zero_smul]
    exact ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm j, List.mem_finRange _, rfl⟩

/-- In any spectral basis, the full projection selects exactly the coordinates
whose eigenvalue equals the chosen ordered value. -/
theorem orderedEigenprojector_diagonalization {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card I)) :
    orderedEigenprojector hA i =
      (hA.eigenvectorUnitary : Matrix I I ℂ) *
        diagonal (fun j => if hA.eigenvalues j = hA.eigenvalues₀ i then (1 : ℂ) else 0) *
        star (hA.eigenvectorUnitary : Matrix I I ℂ) := by
  have hcols : orderedEigenprojector hA i * (hA.eigenvectorUnitary : Matrix I I ℂ) =
      (hA.eigenvectorUnitary : Matrix I I ℂ) *
        diagonal (fun j => if hA.eigenvalues j = hA.eigenvalues₀ i then (1 : ℂ) else 0) := by
    ext a j
    rw [mul_diagonal]
    change (orderedEigenprojector hA i *ᵥ ⇑(hA.eigenvectorBasis j)) a = _
    rw [orderedEigenprojector_mulVec]
    split_ifs <;> simp
  have hU : (hA.eigenvectorUnitary : Matrix I I ℂ) * star (hA.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    hA.eigenvectorUnitary.property.2
  rw [← hcols, mul_assoc, hU, mul_one]

theorem orderedEigenprojector_isHermitian {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card I)) : (orderedEigenprojector hA i).IsHermitian := by
  rw [orderedEigenprojector_diagonalization]
  let D : Matrix I I ℂ := diagonal (fun j => if hA.eigenvalues j = hA.eigenvalues₀ i then 1 else 0)
  have hd : D.IsHermitian := Matrix.isHermitian_diagonal_iff.mpr fun j => by
    split_ifs <;> simp
  let U : Matrix I I ℂ := hA.eigenvectorUnitary
  change (U * D * Uᴴ)ᴴ = U * D * Uᴴ
  rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_mul, hd.eq, mul_assoc]

theorem orderedEigenprojector_idempotent {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card I)) :
    orderedEigenprojector hA i * orderedEigenprojector hA i = orderedEigenprojector hA i := by
  let D : Matrix I I ℂ := diagonal (fun j => if hA.eigenvalues j = hA.eigenvalues₀ i then 1 else 0)
  have hD : D * D = D := by
    dsimp only [D]
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    split_ifs <;> simp
  rw [orderedEigenprojector_diagonalization]
  let U : Matrix I I ℂ := hA.eigenvectorUnitary
  have hU : star U * U = 1 := hA.eigenvectorUnitary.property.1
  change (U * D * star U) * (U * D * star U) = U * D * star U
  calc
    _ = U * D * (star U * U) * D * star U := by simp only [mul_assoc]
    _ = _ := by rw [hU, mul_one, mul_assoc U D D, hD]

/-- Fixing the equality pattern of all ordered eigenvalues gives a measurable
multiplicity stratum, including the strata containing repeated zeros. -/
theorem measurableSet_eigenvalue_stratum {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix I I ℂ) (hA : Measurable A) (hh : ∀ s, (A s).IsHermitian)
    (R : Fin (Fintype.card I) → Fin (Fintype.card I) → Prop) :
    MeasurableSet {s | ∀ i j, (hh s).eigenvalues₀ i = (hh s).eigenvalues₀ j ↔ R i j} := by
  classical
  have h := measurable_ordered_eigenvalues A hA hh
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have he : MeasurableSet {s | (hh s).eigenvalues₀ i = (hh s).eigenvalues₀ j} :=
    measurableSet_eq_fun ((measurable_pi_apply i).comp h) ((measurable_pi_apply j).comp h)
  by_cases hij : R i j
  · simpa only [hij, iff_true] using he
  · simpa only [hij, iff_false, Set.compl_ofPred] using he.compl

end LocalCertification.Quantum
