import LocalCertification.Extremal.EnvelopeUniqueness
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
open scoped BigOperators Topology
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- Coordinates retain the constant-at-infinity component first. -/
def coeffVector (r : ℕ) : CoeffSpace r →ₗ[ℝ] (Fin (r+2) → ℝ) where
  toFun c := Fin.cons c.1 c.2
  map_add' c d := by funext i; cases i using Fin.cases <;> rfl
  map_smul' a c := by funext i; cases i using Fin.cases <;> rfl

theorem coeffVector_injective (r : ℕ) : Function.Injective (coeffVector r) := by
  intro c d h
  apply Prod.ext
  · exact congrFun h 0
  · funext j
    exact congrFun h j.succ

def evaluationMatrix (q : ℝ) (r : ℕ) (x : Fin (r+2) → Option ℝ) :
    Matrix (Fin (r+2)) (Fin (r+2)) ℝ :=
  fun i => coeffVector r (extendedDictionary q r (x i))

theorem evaluationMatrix_det_ne_zero (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+2) → Option ℝ) (hx : Function.Injective x) :
    (evaluationMatrix q r x).det ≠ 0 := by
  have hi := (extendedDictionary_linearIndependent q hq r (r+2) le_rfl x hx).map'
    (coeffVector r) (LinearMap.ker_eq_bot.mpr (coeffVector_injective r))
  have hu : IsUnit (evaluationMatrix q r x) := Matrix.linearIndependent_rows_iff_isUnit.mp hi
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero

def realEvaluationMatrix (q : ℝ) (r : ℕ) (x : Fin (r+2) → ℝ) :
    Matrix (Fin (r+2)) (Fin (r+2)) ℝ := evaluationMatrix q r (fun i => some (x i))

theorem realEvaluationMatrix_det_ne_zero (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+2) → ℝ) (hx : Function.Injective x) :
    (realEvaluationMatrix q r x).det ≠ 0 :=
  evaluationMatrix_det_ne_zero q hq r _ ((Option.some_injective ℝ).comp hx)

theorem realEvaluationMatrix_continuous (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : ℝ → Fin (r+2) → ℝ) (hx : ∀ i, Continuous (fun t => x t i)) :
    Continuous (fun t => realEvaluationMatrix q r (x t)) := by
  apply continuous_matrix
  intro i j
  cases j using Fin.cases with
  | zero => exact continuous_const
  | succ j =>
    change Continuous (fun t => q ^ (-(x t i)) * (x t i)^(j : ℕ))
    simp_rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hq)]
    exact (Real.continuous_exp.comp (continuous_const.mul (hx i).neg)).mul ((hx i).pow _)

/-- A continuous nonvanishing real path has equal endpoint signs. -/
theorem nonzero_path_mul_pos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hn : ∀ t ∈ Icc (0:ℝ) 1, f t ≠ 0) : 0 < f 0 * f 1 := by
  have hn0 := hn 0 (by norm_num)
  have hn1 := hn 1 (by norm_num)
  rcases lt_or_gt_of_ne hn0 with h0 | h0
  · have h1 : f 1 < 0 := by
      by_contra h
      have hz : (0:ℝ) ∈ Icc (f 0) (f 1) := ⟨h0.le, le_of_not_gt h⟩
      obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hf hz
      exact hn t ht he
    exact mul_pos_of_neg_of_neg h0 h1
  · have h1 : 0 < f 1 := by
      by_contra h
      have hz : (0:ℝ) ∈ Icc (f 1) (f 0) := ⟨le_of_not_gt h, h0.le⟩
      obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hf hz
      exact hn t ht he
    exact mul_pos h0 h1

def nodePath {n : ℕ} (x y : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun i => (1-t)*x i+t*y i

theorem nodePath_strictMono {n : ℕ} (x y : Fin n → ℝ) (hx : StrictMono x)
    (hy : StrictMono y) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : StrictMono (nodePath x y t) := by
  intro i j hij
  have hxi := hx hij
  have hyi := hy hij
  dsimp [nodePath]
  by_cases ht0 : t = 0
  · simpa [ht0] using hxi
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hxi.le)
    have h2 := mul_pos htp (sub_pos.mpr hyi)
    nlinarith

/-- Determinants of any two increasingly ordered real node configurations have the same sign. -/
theorem realEvaluationMatrix_det_same_sign (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x y : Fin (r+2) → ℝ) (hx : StrictMono x) (hy : StrictMono y) :
    0 < (realEvaluationMatrix q r x).det * (realEvaluationMatrix q r y).det := by
  have hc : Continuous (fun t => (realEvaluationMatrix q r (nodePath x y t)).det) :=
    (realEvaluationMatrix_continuous q hq r (nodePath x y) (by intro i; unfold nodePath; fun_prop)).matrix_det
  have hn (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (realEvaluationMatrix q r (nodePath x y t)).det ≠ 0 :=
    realEvaluationMatrix_det_ne_zero q hq r _ (nodePath_strictMono x y hx hy ht).injective
  have hp0 : nodePath x y 0 = x := by funext i; simp [nodePath]
  have hp1 : nodePath x y 1 = y := by funext i; simp [nodePath]
  simpa only [hp0, hp1] using nonzero_path_mul_pos hc.continuousOn hn

end LocalCertification.Extremal
