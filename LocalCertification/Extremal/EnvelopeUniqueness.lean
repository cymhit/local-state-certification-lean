import LocalCertification.Extremal.Uniqueness

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- Center and scale the actual envelope interval to the unit interval. -/
def envelopeCandidate (q : ℝ) (r : ℕ) (p : ℝ[X]) : CoeffSpace r :=
  (-(upperEnvelope q p + lowerEnvelope q p)/(upperEnvelope q p-lowerEnvelope q p),
    Polynomial.toFn (r+1) ((2/(upperEnvelope q p-lowerEnvelope q p)) • p))

theorem envelopeCandidate_polynomial (q : ℝ) (r : ℕ) {p : ℝ[X]} (hp : p.natDegree ≤ r) :
    coefficientPolynomial (envelopeCandidate q r p) =
      (2/(upperEnvelope q p-lowerEnvelope q p)) • p :=
  polynomial_reconstruction _ _ ((Polynomial.natDegree_smul_le _ _).trans hp)

theorem polynomialNode_affine (q a h : ℝ) (p : ℝ[X]) (x : OnePoint ℕ) :
    polynomialNode q h (a • p) x = h + a * polynomialNode q 0 p x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe k => simp only [polynomialNode_nat, Polynomial.eval_smul, smul_eq_mul, zero_add]; ring

theorem envelopeCandidate_node (q : ℝ) (r : ℕ) {p : ℝ[X]} (hp : p.natDegree ≤ r)
    (x : OnePoint ℕ) :
    polynomialNode q (envelopeCandidate q r p).1
      (coefficientPolynomial (envelopeCandidate q r p)) x =
      (2 * polynomialNode q 0 p x - (upperEnvelope q p+lowerEnvelope q p)) /
        (upperEnvelope q p-lowerEnvelope q p) := by
  rw [envelopeCandidate_polynomial q r hp, polynomialNode_affine]
  simp only [envelopeCandidate]
  ring

theorem envelopeCandidate_feasible (q : ℝ) (hq : 1 < q) (r : ℕ) {p : ℝ[X]}
    (hp : admissible r p) : envelopeCandidate q r p ∈ feasible q r := by
  intro x
  rw [envelopeCandidate_node q r hp.1]
  have hw := envelope_width_pos q hq hp.2
  have hb := polynomialNode_envelope_bounds q hq p x
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hw).mpr
    linarith
  · apply (div_le_iff₀ hw).mpr
    linarith

theorem envelopeCandidate_extrapolation (q : ℝ) (r : ℕ) {p : ℝ[X]}
    (hp : admissible r p) : extrapolation r (envelopeCandidate q r p) =
      (2-(upperEnvelope q p+lowerEnvelope q p))/(upperEnvelope q p-lowerEnvelope q p) := by
  rw [extrapolation_formula, envelopeCandidate_polynomial q r hp.1,
    Polynomial.eval_smul, hp.2]
  simp only [smul_eq_mul, mul_one, envelopeCandidate]
  ring

theorem envelopeCandidate_maximizes (q : ℝ) (hq : 1 < q) (r : ℕ) {p : ℝ[X]}
    (hp : admissible r p) (hm : envelopeRatio q p = gamma q r) :
    extrapolation r (envelopeCandidate q r p) = extremalValue q r := by
  rw [gamma_eq_extremalValue q hq r] at hm
  have hw := envelope_width_pos q hq hp.2
  have hd := envelope_denominator_pos q hq p
  have hB : 0 < 1+extremalValue q r := by have h := one_lt_extremalValue q hq r; linarith
  have he := (div_eq_div_iff hd.ne' hB.ne').mp hm
  rw [envelopeCandidate_extrapolation q r hp]
  apply (div_eq_iff hw.ne').mpr
  nlinarith

theorem envelopeCandidate_recover (q : ℝ) (hq : 1 < q) (r : ℕ) {p : ℝ[X]}
    (hp : admissible r p) :
    (extrapolation r (envelopeCandidate q r p)-(envelopeCandidate q r p).1)⁻¹ •
      coefficientPolynomial (envelopeCandidate q r p) = p := by
  have hw := envelope_width_pos q hq hp.2
  have hden : extrapolation r (envelopeCandidate q r p)-(envelopeCandidate q r p).1 =
      2/(upperEnvelope q p-lowerEnvelope q p) := by
    rw [extrapolation_formula, envelopeCandidate_polynomial q r hp.1,
      Polynomial.eval_smul, hp.2]
    simp
  rw [hden, envelopeCandidate_polynomial q r hp.1, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (div_pos (by norm_num) hw)), one_smul]

/-- The original envelope minimizer is unique, independently of the B parametrization. -/
theorem envelope_minimizer_unique (q : ℝ) (hq : 1 < q) (r : ℕ) (p t : ℝ[X])
    (hp : admissible r p) (ht : admissible r t)
    (hpm : envelopeRatio q p = gamma q r) (htm : envelopeRatio q t = gamma q r) : p = t := by
  have he := extremizer_unique q hq r (envelopeCandidate q r p) (envelopeCandidate q r t)
    (envelopeCandidate_feasible q hq r hp) (envelopeCandidate_feasible q hq r ht)
    (envelopeCandidate_maximizes q hq r hp hpm) (envelopeCandidate_maximizes q hq r ht htm)
  rw [← envelopeCandidate_recover q hq r hp, he, envelopeCandidate_recover q hq r ht]

theorem existsUnique_envelope_minimizer (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃! p : ℝ[X], admissible r p ∧ envelopeRatio q p = gamma q r := by
  obtain ⟨p, hp, hm⟩ := gamma_attained q hq r
  exact ⟨p, ⟨hp, hm⟩, fun t ht => envelope_minimizer_unique q hq r t p ht.1 hp ht.2 hm⟩

end LocalCertification.Extremal
