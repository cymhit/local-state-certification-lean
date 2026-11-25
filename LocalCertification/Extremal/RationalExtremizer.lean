import LocalCertification.Extremal.ElementaryDecay

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- The actual integer/infinity evaluation matrix, formed over the rationals. -/
def rationalEvaluationMatrix (q : ℚ) (r : ℕ) (x : Fin (r+2) → OnePoint ℕ) :
    Matrix (Fin (r+2)) (Fin (r+2)) ℚ :=
  fun i => Fin.cons 1 (fun j => (x i).elim 0 (fun k => (q⁻¹)^(k+1)*((k+1 : ℕ) : ℚ)^(j : ℕ)))

theorem rationalEvaluationMatrix_cast (q : ℚ) (r : ℕ) (x : Fin (r+2) → OnePoint ℕ) :
    (rationalEvaluationMatrix q r x).map (Rat.castHom ℝ) =
      evaluationMatrix (q : ℝ) r (fun i => nodeToExtended (x i)) := by
  ext i j
  simp only [evaluationMatrix, extendedDictionary_nodeToExtended]
  cases j using Fin.cases with
  | zero => simp [rationalEvaluationMatrix, coeffVector, evaluationDictionary]
  | succ j =>
    simp only [rationalEvaluationMatrix, Matrix.map_apply, Fin.cons_succ]
    induction x i using OnePoint.rec with
    | infty => simp [coeffVector, evaluationDictionary_infty]
    | coe k => simp [coeffVector, evaluationDictionary_nat]

theorem rationalEvaluationMatrix_det_ne_zero (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ)
    (x : Fin (r+2) → OnePoint ℕ) (hx : Function.Injective x) :
    (rationalEvaluationMatrix q r x).det ≠ 0 := by
  have h := (Rat.castHom ℝ).map_det (rationalEvaluationMatrix q r x)
  change ((rationalEvaluationMatrix q r x).det : ℝ) =
    ((rationalEvaluationMatrix q r x).map (Rat.castHom ℝ)).det at h
  rw [rationalEvaluationMatrix_cast] at h
  intro hz
  have hn := evaluationMatrix_det_ne_zero (q : ℝ) hq r (fun i => nodeToExtended (x i))
    (nodeToExtended_injective.comp hx)
  rw [hz, Rat.cast_zero] at h
  exact hn h.symm

theorem pairing_coeffVector {r : ℕ} (c d : CoeffSpace r) :
    dotProduct (coeffVector r c) (coeffVector r d) = pairing c d := by
  simp [dotProduct, Fin.sum_univ_succ, coeffVector, pairing]

theorem evaluationMatrix_mulVec {r : ℕ} (q : ℝ) (x : Fin (r+2) → Option ℝ)
    (c : CoeffSpace r) (i : Fin (r+2)) :
    (evaluationMatrix q r x).mulVec (coeffVector r c) i =
      extendedFunction q c.1 (coefficientPolynomial c) (x i) := by
  change dotProduct (coeffVector r (extendedDictionary q r (x i))) (coeffVector r c) = _
  rw [pairing_coeffVector, pairing_comm, pairing_extendedDictionary]

/-- Rational values at actual distinct nodes force rational coefficients; Cramer is used over ℚ. -/
theorem rational_coefficients_of_values (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ)
    (x : Fin (r+2) → OnePoint ℕ) (hx : Function.Injective x)
    (v : Fin (r+2) → ℚ) (c : CoeffSpace r)
    (hv : ∀ i, polynomialNode (q : ℝ) c.1 (coefficientPolynomial c) (x i) = (v i : ℝ)) :
    ∃ (a : ℚ) (b : Fin (r+1) → ℚ), c = ((a : ℝ), fun j => (b j : ℝ)) := by
  classical
  let A := rationalEvaluationMatrix q r x
  let y : Fin (r+2) → ℚ := A.det⁻¹ • A.cramer v
  have hd : A.det ≠ 0 := rationalEvaluationMatrix_det_ne_zero q hq r x hx
  have hy : A.mulVec y = v := by
    dsimp [y]
    rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hd, one_smul]
  let E := evaluationMatrix (q : ℝ) r (fun i => nodeToExtended (x i))
  have hcast : A.map (Rat.castHom ℝ) = E := rationalEvaluationMatrix_cast q r x
  have hyr : E.mulVec (fun i => (y i : ℝ)) = fun i => (v i : ℝ) := by
    funext i
    rw [← hcast]
    have h := (Rat.castHom ℝ).map_mulVec A y i
    rw [hy] at h
    exact h.symm
  have hcr : E.mulVec (coeffVector r c) = fun i => (v i : ℝ) := by
    funext i
    exact (evaluationMatrix_mulVec (q : ℝ) _ c i).trans ((extendedFunction_nodeToExtended _ _ _ _).trans (hv i))
  have hunit : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).mpr
    (isUnit_iff_ne_zero.mpr (evaluationMatrix_det_ne_zero (q : ℝ) hq r _ (nodeToExtended_injective.comp hx)))
  have he := (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (hyr.trans hcr.symm)
  refine ⟨y 0, fun j => y j.succ, ?_⟩
  apply Prod.ext
  · exact (congrFun he 0).symm
  · funext j
    exact (congrFun he j.succ).symm

theorem extremizer_coefficients_rational (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ)
    (c : CoeffSpace r) (hc : c ∈ feasible (q : ℝ) r)
    (hm : extrapolation r c = extremalValue (q : ℝ) r) :
    ∃ (a : ℚ) (b : Fin (r+1) → ℚ), c = ((a : ℝ), fun j => (b j : ℝ)) := by
  obtain ⟨d, x, μ, hd, hdm, hx, _, _, _, _, _, _, hcontact, _, _⟩ := finite_extremal_dual_complete (q : ℝ) hq r
  have hcd := extremizer_unique (q : ℝ) hq r c d hc hd hm hdm
  subst c
  apply rational_coefficients_of_values q hq r x hx (fun i => (-1 : ℚ)^(i : ℕ)) d
  intro i
  simpa using hcontact i

theorem extremalValue_rational (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ) :
    ∃ B : ℚ, (B : ℝ) = extremalValue (q : ℝ) r := by
  obtain ⟨c, hc, hm⟩ := extremalValue_attained (q : ℝ) hq r
  obtain ⟨a, b, hcb⟩ := extremizer_coefficients_rational q hq r c hc hm
  subst c
  refine ⟨a + ∑ j, b j * (0 : ℚ)^(j : ℕ), ?_⟩
  simpa [extrapolation_formula, coefficientPolynomial_eval] using hm

theorem gamma_rational (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ) :
    ∃ g : ℚ, (g : ℝ) = gamma (q : ℝ) r := by
  obtain ⟨B, hB⟩ := extremalValue_rational q hq r
  refine ⟨2/(1+B), ?_⟩
  rw [gamma_eq_extremalValue (q : ℝ) hq r, ← hB]
  push_cast
  rfl

theorem coefficientPolynomial_ratCast (r : ℕ) (a : ℚ) (b : Fin (r+1) → ℚ) :
    (Polynomial.ofFn (r+1) b).map (Rat.castHom ℝ) =
      coefficientPolynomial (r := r) ((a : ℝ), fun j => (b j : ℝ)) := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < r+1
  · simp [coefficientPolynomial, hk]
  · have hge : r+1 ≤ k := le_of_not_gt hk
    simp [coefficientPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ hge]

theorem extremizerPolynomial_rational (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ)
    (c : CoeffSpace r) (hc : c ∈ feasible (q : ℝ) r)
    (hm : extrapolation r c = extremalValue (q : ℝ) r) :
    ∃ p : ℚ[X], p.map (Rat.castHom ℝ) = extremizerPolynomial (q : ℝ) r c := by
  obtain ⟨a, b, hcb⟩ := extremizer_coefficients_rational q hq r c hc hm
  obtain ⟨B, hB⟩ := extremalValue_rational q hq r
  subst c
  refine ⟨(B-a)⁻¹ • Polynomial.ofFn (r+1) b, ?_⟩
  rw [Polynomial.map_smul, coefficientPolynomial_ratCast r a b]
  simp only [extremizerPolynomial, map_inv₀, map_sub, Rat.coe_castHom, hB]

theorem envelope_minimizer_rational (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ) (p : ℝ[X])
    (hp : admissible r p) (hm : envelopeRatio (q : ℝ) p = gamma (q : ℝ) r) :
    ∃ P : ℚ[X], P.map (Rat.castHom ℝ) = p := by
  obtain ⟨c, hc, hcm⟩ := extremalValue_attained (q : ℝ) hq r
  have hpc := extremizerPolynomial_admissible (q : ℝ) hq r hc hcm
  have hmc : envelopeRatio (q : ℝ) (extremizerPolynomial (q : ℝ) r c) = gamma (q : ℝ) r := by
    rw [gamma_eq_extremalValue (q : ℝ) hq r]
    exact le_antisymm (extremizerPolynomial_ratio_le (q : ℝ) hq r hc)
      (envelopeRatio_lower (q : ℝ) hq r hpc)
  have he := envelope_minimizer_unique (q : ℝ) hq r p (extremizerPolynomial (q : ℝ) r c) hp hpc hm hmc
  obtain ⟨P, hP⟩ := extremizerPolynomial_rational q hq r c hc hcm
  exact ⟨P, hP.trans he.symm⟩

end LocalCertification.Extremal
