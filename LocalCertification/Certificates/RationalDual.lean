import LocalCertification.Certificates.Soundness

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Certificates

/-- Exact dual weights are rational: solve the actual transposed evaluation system over ℚ. -/
theorem rational_dual_weights (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ)
    (x : Fin (r+2) → OnePoint ℕ) (hx : Function.Injective x)
    (μ : Fin (r+2) → ℝ)
    (he : ∀ c : CoeffSpace r, extrapolation r c =
      ∑ i, μ i*polynomialNode (q : ℝ) c.1 (coefficientPolynomial c) (x i)) :
    ∃ ν : Fin (r+2) → ℚ, ∀ i, (ν i : ℝ) = μ i := by
  classical
  let A := (rationalEvaluationMatrix q r x).transpose
  let v : Fin (r+2) → ℚ := Fin.cons 1 (fun j : Fin (r+1) => (0 : ℚ)^j.val)
  let ν : Fin (r+2) → ℚ := A.det⁻¹ • A.cramer v
  have hd : A.det ≠ 0 := by
    simpa [A] using rationalEvaluationMatrix_det_ne_zero q hq r x hx
  have hν : A.mulVec ν = v := by
    dsimp [ν]
    rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hd, one_smul]
  let E := A.map (Rat.castHom ℝ)
  have hνR : E.mulVec (fun i => (ν i : ℝ)) = fun i => (v i : ℝ) := by
    funext i
    have h := (Rat.castHom ℝ).map_mulVec A ν i
    rw [hν] at h
    exact h.symm
  have hμR : E.mulVec μ = fun i => (v i : ℝ) := by
    funext j
    cases j using Fin.cases with
    | zero =>
      simpa [E, A, v, Matrix.mulVec, dotProduct, rationalEvaluationMatrix] using
        finite_dual_mass (q : ℝ) r x μ he
    | succ j =>
      have h := finite_dual_monomial_moments (q : ℝ) r x μ he j.val (by omega)
      have hm (i : Fin (r+2)) : E j.succ i = nodeMonomial (q : ℝ) j.val (x i) := by
        change (rationalNodeMonomial q j.val (x i) : ℝ) = _
        exact rationalNodeMonomial_cast q j.val (x i)
      simp only [Matrix.mulVec, dotProduct, hm]
      by_cases hj : j.val = 0 <;> simpa [v, mul_comm, hj, zero_pow] using h
  have hEd : E.det ≠ 0 := by
    have hc := (Rat.castHom ℝ).map_det A
    change (A.det : ℝ) = E.det at hc
    rw [← hc]
    exact_mod_cast hd
  have hunit : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).mpr (isUnit_iff_ne_zero.mpr hEd)
  have hsame := (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (hνR.trans hμR.symm)
  exact ⟨ν, fun i => congrFun hsame i⟩

/-- Rational dual weights satisfy the finite exact mass and moment checks used by the executable certificate. -/
theorem rational_dual_finite_checks (q : ℚ) (r n : ℕ)
    (x : Fin n → OnePoint ℕ) (ν : Fin n → ℚ)
    (he : ∀ c : CoeffSpace r, extrapolation r c =
      ∑ i, (ν i : ℝ)*polynomialNode (q : ℝ) c.1 (coefficientPolynomial c) (x i)) :
    (∑ i, ν i = 1) ∧
      ∀ j : Fin (r+1), ∑ i, ν i*rationalNodeMonomial q j.val (x i) = (0 : ℚ)^j.val := by
  constructor
  · exact_mod_cast finite_dual_mass (q : ℝ) r x (fun i => (ν i : ℝ)) he
  · intro j
    have h := finite_dual_monomial_moments (q : ℝ) r x (fun i => (ν i : ℝ)) he j.val (by omega)
    have hr : ∑ i, (ν i : ℝ)*(rationalNodeMonomial q j.val (x i) : ℝ) = (0 : ℝ)^j.val := by
      simp only [rationalNodeMonomial_cast]
      by_cases hj : j.val = 0 <;> simpa [hj, zero_pow] using h
    exact_mod_cast hr

end LocalCertification.Certificates
