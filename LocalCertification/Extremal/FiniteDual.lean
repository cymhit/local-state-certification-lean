import LocalCertification.Extremal.ContactHull

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
noncomputable section
namespace LocalCertification.Extremal

/-- A real signed atomic dual for every maximizer, obtained from actual contact-hull membership.
The exact support size, infinity membership and alternation are later interpolation results. -/
theorem finite_dual_of_extremizer (q : ℝ) (hq : 1 < q) (r : ℕ)
    {c : CoeffSpace r} (hc : c ∈ feasible q r) (hmax : extrapolation r c = extremalValue q r) :
    ∃ (n : ℕ) (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ),
      Function.Injective x ∧ (∀ i, μ i ≠ 0) ∧ n ≤ r + 2 ∧
      (∀ b : CoeffSpace r, extrapolation r b =
        ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i)) ∧
      (∑ i, |μ i| = extremalValue q r) ∧
      (∀ i, μ i * polynomialNode q c.1 (coefficientPolynomial c) (x i) = |μ i|) := by
  obtain ⟨n, x, ε, a, hx, hε, hcontact, ha, hsum, he, hl, hn⟩ :=
    contact_nodes_compression q r c (normalizedExtrapolation_mem_contactHull q hq r hc hmax)
  have hB : 0 < extremalValue q r := lt_trans zero_lt_one (one_lt_extremalValue q hq r)
  let μ : Fin n → ℝ := fun i => extremalValue q r * a i * ε i
  have habs (i : Fin n) : |μ i| = extremalValue q r * a i := by
    rcases hε i with hi | hi <;> simp [μ, hi, abs_of_pos (mul_pos hB (ha i))]
  have hvec : ∑ i, μ i • evaluationDictionary q r (x i) = extrapolationDictionary r := by
    have h := congrArg (fun v : CoeffSpace r => extremalValue q r • v) he
    simpa [μ, Finset.smul_sum, smul_smul, normalizedExtrapolation, hB.ne', mul_assoc] using h
  refine ⟨n, x, μ, hx, ?_, hn, ?_, ?_, ?_⟩
  · intro i hzero
    have h := habs i
    rw [hzero, abs_zero] at h
    exact (ne_of_gt (mul_pos hB (ha i))) h.symm
  · intro b
    have h := congrArg (pairing b) hvec
    simp only [map_sum, map_smul, smul_eq_mul, pairing_dictionary] at h
    rw [pairing_comm] at h
    exact h.symm
  · simp_rw [habs]
    rw [← Finset.mul_sum, hsum, mul_one]
  · intro i
    rw [hcontact i, habs i]
    rcases hε i with hi | hi <;> simp [μ, hi]

theorem finite_extremal_dual (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ (c : CoeffSpace r) (n : ℕ) (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ),
      c ∈ feasible q r ∧ extrapolation r c = extremalValue q r ∧
      Function.Injective x ∧ (∀ i, μ i ≠ 0) ∧ n ≤ r + 2 ∧
      (∀ b : CoeffSpace r, extrapolation r b =
        ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i)) ∧
      (∑ i, |μ i| = extremalValue q r) ∧
      (∀ i, μ i * polynomialNode q c.1 (coefficientPolynomial c) (x i) = |μ i|) := by
  obtain ⟨c, hc, hmax⟩ := extremalValue_attained q hq r
  obtain ⟨n, x, μ, hx, hμ, hn, he, hv, hcontact⟩ := finite_dual_of_extremizer q hq r hc hmax
  exact ⟨c, n, x, μ, hc, hmax, hx, hμ, hn, he, hv, hcontact⟩


theorem polynomialNode_zero (q h : ℝ) (x : OnePoint ℕ) : polynomialNode q h 0 x = h := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe k => simp

theorem finite_dual_mass {n : ℕ} (q : ℝ) (r : ℕ) (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i)) : ∑ i, μ i = 1 := by
  have h := he (1, 0)
  simpa [extrapolation_formula, coefficientPolynomial, polynomialNode_zero] using h.symm

theorem finite_dual_polynomial {n : ℕ} (q : ℝ) (r : ℕ) (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i))
    (p : Polynomial ℝ) (hp : p.natDegree ≤ r) :
    p.eval 0 = ∑ i, μ i * polynomialNode q 0 p (x i) := by
  have h := he (0, Polynomial.toFn (r+1) p)
  simpa only [extrapolation_formula, polynomial_reconstruction 0 p hp, zero_add] using h

theorem finite_dual_monomial_moments {n : ℕ} (q : ℝ) (r : ℕ)
    (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i))
    (j : ℕ) (hj : j ≤ r) :
    ∑ i, μ i * nodeMonomial q j (x i) = if j = 0 then 1 else 0 := by
  have h := finite_dual_polynomial q r x μ he (Polynomial.X ^ j) (by simpa using hj)
  have hf : polynomialNode q 0 (Polynomial.X ^ j) = nodeMonomial q j := by
    funext t
    induction t using OnePoint.rec with
    | infty => rfl
    | coe k => simp [nodeMonomial]
  rw [hf] at h
  by_cases hj0 : j = 0 <;> simpa [hj0] using h.symm

end LocalCertification.Extremal
