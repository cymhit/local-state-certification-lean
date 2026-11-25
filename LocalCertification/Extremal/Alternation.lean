import LocalCertification.Extremal.OrderedMatrix

set_option autoImplicit false
open scoped BigOperators Topology
open Set
noncomputable section
namespace LocalCertification.Extremal

theorem pairing_ext {r : ℕ} {v w : CoeffSpace r}
    (h : ∀ c : CoeffSpace r, pairing c v = pairing c w) : v = w := by
  classical
  apply Prod.ext
  · simpa [pairing] using h (1, 0)
  · funext j
    simpa [pairing, Pi.single_apply] using h (0, Pi.single j 1)

/-- Scalar reproduction for every actual coefficient is a vector reproduction identity. -/
theorem reproduction_dictionary {r : ℕ} {n : ℕ} (q : ℝ)
    (x : Fin n → Option ℝ) (μ : Fin n → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * extendedFunction q b.1 (coefficientPolynomial b) (x i)) :
    extendedDictionary q r (some 0) = ∑ i, μ i • extendedDictionary q r (x i) := by
  apply pairing_ext
  intro b
  simp only [map_sum, map_smul, smul_eq_mul, pairing_extendedDictionary]
  simpa [extendedFunction, realFunction, extrapolation_formula] using he b

theorem reproduced_update_det (q : ℝ) (r : ℕ) (x : Fin (r+2) → Option ℝ)
    (μ : Fin (r+2) → ℝ)
    (he : extendedDictionary q r (some 0) = ∑ i, μ i • extendedDictionary q r (x i))
    (j : Fin (r+2)) :
    ((evaluationMatrix q r x).updateRow j (coeffVector r (extendedDictionary q r (some 0)))).det =
      μ j * (evaluationMatrix q r x).det := by
  have hv := congrArg (coeffVector r) he
  simp only [map_sum, map_smul] at hv
  rw [hv]
  exact Matrix.det_updateRow_sum _ j μ

theorem prepend_delete_det (q : ℝ) (r : ℕ) (x : Fin (r+2) → Option ℝ) (j : Fin (r+2)) :
    (evaluationMatrix q r (Fin.cons (some 0) (fun i => x (j.succAbove i)))).det =
      (-1 : ℝ)^(j : ℕ) *
        ((evaluationMatrix q r x).updateRow j (coeffVector r (extendedDictionary q r (some 0)))).det := by
  classical
  have he : evaluationMatrix q r (Fin.cons (some 0) (fun i => x (j.succAbove i))) =
      ((evaluationMatrix q r x).updateRow j (coeffVector r (extendedDictionary q r (some 0)))).submatrix
        j.cycleRange.symm id := by
    ext i k
    cases i using Fin.cases with
    | zero =>
      simp only [evaluationMatrix, Matrix.submatrix, Fin.cons_zero, Fin.cycleRange_symm_zero, id_eq, Matrix.updateRow, Matrix.of_apply]
      simp [Function.update]
    | succ i =>
      simp only [evaluationMatrix, Matrix.submatrix, Fin.cons_succ, Fin.cycleRange_symm_succ, id_eq, Matrix.updateRow, Matrix.of_apply]
      simp only [Function.update, dite_eq_right (Fin.succAbove_ne j i)]
      rfl
  rw [he, Matrix.det_permute]
  simp

/-- Signed weights of every exact ordered extrapolation formula alternate, beginning positive. -/
theorem ordered_reproduction_alternating (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+2) → Option ℝ) (hx : OrderedExtendedNodes x)
    (hp : ∀ i, (0 : WithTop ℝ) < optionOrder (x i)) (μ : Fin (r+2) → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * extendedFunction q b.1 (coefficientPolynomial b) (x i)) :
    ∀ j : Fin (r+2), 0 < (-1 : ℝ)^(j : ℕ) * μ j := by
  intro j
  have hsign := orderedEvaluationMatrix_det_same_sign q hq r x
    (Fin.cons (some 0) (fun i => x (j.succAbove i))) hx (ordered_replace_prepend r x hx hp j)
  rw [prepend_delete_det, reproduced_update_det q r x μ (reproduction_dictionary q x μ he)] at hsign
  have hd : 0 < (evaluationMatrix q r x).det ^ 2 :=
    sq_pos_of_ne_zero (evaluationMatrix_det_ne_zero q hq r x (orderedExtendedNodes_injective hx))
  have hmul : 0 < ((-1 : ℝ)^(j : ℕ) * μ j) * (evaluationMatrix q r x).det ^ 2 := by
    nlinarith [hsign]
  exact (mul_pos_iff_of_pos_right hd).mp hmul

end LocalCertification.Extremal
