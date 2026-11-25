import LocalCertification.Extremal.InfinitySupport

set_option autoImplicit false
open scoped BigOperators Topology
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

def degreeEmbedding (r : ℕ) (c : CoeffSpace r) : CoeffSpace (r+1) :=
  (c.1, Polynomial.toFn (r+1+1) (coefficientPolynomial c))

theorem degreeEmbedding_polynomial (r : ℕ) (c : CoeffSpace r) :
    coefficientPolynomial (degreeEmbedding r c) = coefficientPolynomial c :=
  polynomial_reconstruction _ _ ((coefficientPolynomial_degree c).trans (Nat.le_succ r))

theorem degreeEmbedding_feasible (q : ℝ) (r : ℕ) (c : CoeffSpace r)
    (hc : c ∈ feasible q r) : degreeEmbedding r c ∈ feasible q (r+1) := by
  intro x
  change |polynomialNode q c.1 (coefficientPolynomial (degreeEmbedding r c)) x| ≤ 1
  rw [degreeEmbedding_polynomial]
  exact hc x

theorem degreeEmbedding_extrapolation (r : ℕ) (c : CoeffSpace r) :
    extrapolation (r+1) (degreeEmbedding r c) = extrapolation r c := by
  rw [extrapolation_formula, extrapolation_formula, degreeEmbedding_polynomial]
  rfl

/-- The increase is strict because equality would make a lower-degree function optimal. -/
theorem extremalValue_strict_succ (q : ℝ) (hq : 1 < q) (r : ℕ) :
    extremalValue q r < extremalValue q (r+1) := by
  obtain ⟨c, hc, hm⟩ := extremalValue_attained q hq r
  have hd := degreeEmbedding_feasible q r c hc
  have he : extrapolation (r+1) (degreeEmbedding r c) = extremalValue q r :=
    (degreeEmbedding_extrapolation r c).trans hm
  have hle : extremalValue q r ≤ extremalValue q (r+1) := by
    rw [← he]
    exact extrapolation_le_extremalValue q hq (r+1) hd
  by_contra hnot
  have heq : extremalValue q r = extremalValue q (r+1) := le_antisymm hle (le_of_not_gt hnot)
  have hdeg := extremizer_polynomial_degree q hq (r+1) (degreeEmbedding r c) hd (he.trans heq)
  rw [degreeEmbedding_polynomial] at hdeg
  have hbound := coefficientPolynomial_degree c
  omega

theorem extremalValue_strictMono (q : ℝ) (hq : 1 < q) : StrictMono (extremalValue q) :=
  strictMono_nat_of_lt_succ (extremalValue_strict_succ q hq)

theorem gamma_strict_succ (q : ℝ) (hq : 1 < q) (r : ℕ) : gamma q (r+1) < gamma q r := by
  rw [gamma_eq_extremalValue q hq (r+1), gamma_eq_extremalValue q hq r]
  have h0 : 0 < 1+extremalValue q r := by have h := one_lt_extremalValue q hq r; linarith
  have h1 : 0 < 1+extremalValue q (r+1) := by have h := one_lt_extremalValue q hq (r+1); linarith
  apply (div_lt_div_iff₀ h1 h0).mpr
  have h := extremalValue_strict_succ q hq r
  linarith

theorem gamma_strictAnti (q : ℝ) (hq : 1 < q) : StrictAnti (gamma q) :=
  strictAnti_nat_of_succ_lt (gamma_strict_succ q hq)

theorem extremizer_polynomial_ne_zero (q : ℝ) (hq : 1 < q) (r : ℕ) (c : CoeffSpace r)
    (hc : c ∈ feasible q r) (hm : extrapolation r c = extremalValue q r) :
    coefficientPolynomial c ≠ 0 := by
  intro hp
  have hh : |c.1| ≤ 1 := hc OnePoint.infty
  have hB := one_lt_extremalValue q hq r
  rw [extrapolation_formula, hp, Polynomial.eval_zero, add_zero] at hm
  have hu := (abs_le.mp hh).2
  linarith

theorem extremizer_polynomial_degree_eq (q : ℝ) (hq : 1 < q) (r : ℕ) (c : CoeffSpace r)
    (hc : c ∈ feasible q r) (hm : extrapolation r c = extremalValue q r) :
    (coefficientPolynomial c).degree = (r : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (extremizer_polynomial_ne_zero q hq r c hc hm),
    extremizer_polynomial_degree q hq r c hc hm]

theorem envelope_minimizer_degree_eq (q : ℝ) (hq : 1 < q) (r : ℕ) (p : ℝ[X])
    (hp : admissible r p) (hm : envelopeRatio q p = gamma q r) : p.degree = (r : WithBot ℕ) := by
  have hn : p ≠ 0 := by intro h; simpa [h] using hp.2
  rw [Polynomial.degree_eq_natDegree hn, envelope_minimizer_degree q hq r p hp hm]

end LocalCertification.Extremal
