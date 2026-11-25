import LocalCertification.Extremal.EvaluationMatrix

set_option autoImplicit false
open scoped BigOperators Topology
open Set Filter
noncomputable section
namespace LocalCertification.Extremal

def infinityEvaluationMatrix (q : ℝ) (r : ℕ) (x : Fin (r+1) → ℝ) :
    Matrix (Fin (r+2)) (Fin (r+2)) ℝ :=
  evaluationMatrix q r (Fin.snoc (fun i => some (x i)) none)

theorem infinityEvaluationMatrix_det_ne_zero (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+1) → ℝ) (hx : Function.Injective x) :
    (infinityEvaluationMatrix q r x).det ≠ 0 :=
  evaluationMatrix_det_ne_zero q hq r _ (Fin.snoc_injective_of_injective
    ((Option.some_injective ℝ).comp hx) (by simp))

theorem realEvaluationMatrix_snoc_tendsto (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+1) → ℝ) :
    Tendsto (fun n : ℕ => realEvaluationMatrix q r (Fin.snoc x (n : ℝ)))
      atTop (𝓝 (infinityEvaluationMatrix q r x)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  cases i using Fin.lastCases with
  | cast i =>
    simpa only [realEvaluationMatrix, infinityEvaluationMatrix, evaluationMatrix,
      Fin.snoc_castSucc] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => coeffVector r (extendedDictionary q r (some (x i))) j)
        atTop (𝓝 (coeffVector r (extendedDictionary q r (some (x i))) j)))
  | last =>
    cases j using Fin.cases with
    | zero =>
      simp [realEvaluationMatrix, infinityEvaluationMatrix, evaluationMatrix,
        extendedDictionary, coeffVector]
    | succ j =>
      simpa [realEvaluationMatrix, infinityEvaluationMatrix, evaluationMatrix,
        extendedDictionary, coeffVector, inverse_pow_eq_real_decay] using
        monomial_decay_tendsto q hq (j : ℕ)

theorem strictMono_snoc {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) (b : ℝ)
    (hb : ∀ i, x i < b) : StrictMono (Fin.snoc x b) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last => exact (not_lt_of_ge (Fin.le_last _) hij).elim
  | cast i =>
    cases j using Fin.lastCases with
    | last => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hb i
    | cast j => simpa only [Fin.snoc_castSucc] using hx (Fin.castSucc_lt_castSucc_iff.mp hij)

theorem eventually_strictMono_snoc (r : ℕ) (x : Fin (r+1) → ℝ) (hx : StrictMono x) :
    ∀ᶠ n : ℕ in atTop, StrictMono (Fin.snoc x (n : ℝ)) := by
  have h : ∀ᶠ n : ℕ in atTop, ∀ i, x i < (n : ℝ) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop (x i))
  exact h.mono (fun n hn => strictMono_snoc x hx n hn)

/-- The finite-node orientation persists when the last node tends to infinity. -/
theorem real_infinity_det_same_sign (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+2) → ℝ) (y : Fin (r+1) → ℝ) (hx : StrictMono x) (hy : StrictMono y) :
    0 < (realEvaluationMatrix q r x).det * (infinityEvaluationMatrix q r y).det := by
  have hd : Tendsto (fun n : ℕ => (realEvaluationMatrix q r (Fin.snoc y (n : ℝ))).det)
      atTop (𝓝 (infinityEvaluationMatrix q r y).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp (realEvaluationMatrix_snoc_tendsto q hq r y)
  have hle : 0 ≤ (realEvaluationMatrix q r x).det * (infinityEvaluationMatrix q r y).det := by
    apply ge_of_tendsto (tendsto_const_nhds.mul hd)
    exact (eventually_strictMono_snoc r y hy).mono
      (fun n hn => (realEvaluationMatrix_det_same_sign q hq r x _ hx hn).le)
  exact lt_of_le_of_ne hle (Ne.symm (mul_ne_zero
    (realEvaluationMatrix_det_ne_zero q hq r x hx.injective)
    (infinityEvaluationMatrix_det_ne_zero q hq r y hy.injective)))

end LocalCertification.Extremal
