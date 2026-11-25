import LocalCertification.Extremal.LagrangeSigns

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

theorem polynomial_eval_of_real_contact (q : ℝ) (hq : 0 < q) (h s w : ℝ) (p : ℝ[X])
    (he : realFunction q h p w = s) : p.eval w = q^w * (s-h) := by
  have hc : q^w*q^(-w) = (1:ℝ) := by rw [← Real.rpow_add hq]; simp
  have hi := congrArg (fun t => q^w*t) he
  simp only [realFunction, mul_add] at hi
  rw [← mul_assoc, hc, one_mul] at hi
  linarith

/-- Alternating contacts of a feasible model cannot all be finite. -/
theorem alternating_contacts_infinity (q : ℝ) (hq : 1 < q) (r : ℕ)
    (c : CoeffSpace r) (hc : c ∈ feasible q r) (x : Fin (r+2) → OnePoint ℕ)
    (hx : OrderedExtendedNodes (fun i => nodeToExtended (x i)))
    (he : ∀ i : Fin (r+2), polynomialNode q c.1 (coefficientPolynomial c) (x i) = (-1 : ℝ)^(i : ℕ)) :
    x (Fin.last (r+1)) = ∞ := by
  rcases orderedExtendedNodes_cases r (fun i => nodeToExtended (x i)) hx with
    ⟨y, hy, hey⟩ | ⟨y, hy, hey⟩
  · have hnodes (i : Fin (r+2)) : (coefficientPolynomial c).eval (y i) =
        q^(y i)*((-1 : ℝ)^(i : ℕ)-c.1) := by
      apply polynomial_eval_of_real_contact q (lt_trans zero_lt_one hq)
      have hi := he i
      rw [← extendedFunction_nodeToExtended, congrFun hey i] at hi
      exact hi
    have hdegree := alternating_offset_degree_lower (r+1) (by omega) y hy (fun i => q^(y i))
      (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hq) _) c.1 (hc ∞)
      (coefficientPolynomial c) hnodes
    have hp := coefficientPolynomial_degree c
    omega
  · apply nodeToExtended_injective
    change nodeToExtended (x (Fin.last (r+1))) = none
    simpa using congrFun hey (Fin.last (r+1))

theorem alternating_contacts_degree (q : ℝ) (hq : 1 < q) (r : ℕ)
    (c : CoeffSpace r) (hc : c ∈ feasible q r) (x : Fin (r+2) → OnePoint ℕ)
    (hx : OrderedExtendedNodes (fun i => nodeToExtended (x i)))
    (he : ∀ i : Fin (r+2), polynomialNode q c.1 (coefficientPolynomial c) (x i) = (-1 : ℝ)^(i : ℕ)) :
    (coefficientPolynomial c).natDegree = r := by
  apply le_antisymm (coefficientPolynomial_degree c)
  by_cases hr : r = 0
  · simp [hr]
  have hinf := alternating_contacts_infinity q hq r c hc x hx he
  rcases orderedExtendedNodes_cases r (fun i => nodeToExtended (x i)) hx with
    ⟨y, hy, hey⟩ | ⟨y, hy, hey⟩
  · have hi := congrFun hey (Fin.last (r+1))
    simp [hinf, nodeToExtended] at hi
  · apply alternating_offset_degree_lower r (by omega) y hy (fun i => q^(y i))
      (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hq) _) c.1 (hc ∞) (coefficientPolynomial c)
    intro i
    apply polynomial_eval_of_real_contact q (lt_trans zero_lt_one hq)
    have hi := he i.castSucc
    rw [← extendedFunction_nodeToExtended, congrFun hey i.castSucc] at hi
    simpa only [Fin.snoc_castSucc, Fin.val_castSucc, extendedFunction, Option.elim_some] using hi

/-- Fully supported norming dual: exact cardinality, nonzero infinity atom, and alternation. -/
theorem finite_extremal_dual_complete (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ (c : CoeffSpace r) (x : Fin (r+2) → OnePoint ℕ) (μ : Fin (r+2) → ℝ),
      c ∈ feasible q r ∧ extrapolation r c = extremalValue q r ∧
      Function.Injective x ∧ OrderedExtendedNodes (fun i => nodeToExtended (x i)) ∧
      x (Fin.last (r+1)) = ∞ ∧ (∀ i, μ i ≠ 0) ∧
      (∀ b : CoeffSpace r, extrapolation r b =
        ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i)) ∧
      (∑ i, |μ i| = extremalValue q r) ∧
      (∀ i : Fin (r+2), 0 < (-1 : ℝ)^(i : ℕ) * μ i) ∧
      (∀ i : Fin (r+2), polynomialNode q c.1 (coefficientPolynomial c) (x i) = (-1 : ℝ)^(i : ℕ)) ∧
      c.1 = (-1 : ℝ)^(r+1) ∧ (coefficientPolynomial c).natDegree = r := by
  obtain ⟨c, x, μ, hc, hm, hx, ho, hμ, he, hv, hs, hcontact⟩ := finite_extremal_dual_ordered q hq r
  have hinf := alternating_contacts_infinity q hq r c hc x ho hcontact
  refine ⟨c, x, μ, hc, hm, hx, ho, hinf, hμ, he, hv, hs, hcontact, ?_,
    alternating_contacts_degree q hq r c hc x ho hcontact⟩
  simpa [hinf] using hcontact (Fin.last (r+1))

theorem extremizer_limit_value (q : ℝ) (hq : 1 < q) (r : ℕ) (c : CoeffSpace r)
    (hc : c ∈ feasible q r) (hm : extrapolation r c = extremalValue q r) :
    c.1 = (-1 : ℝ)^(r+1) := by
  obtain ⟨d, x, μ, hd, hdm, _, _, _, _, _, _, _, _, hlimit, _⟩ := finite_extremal_dual_complete q hq r
  rw [extremizer_unique q hq r c d hc hd hm hdm]
  exact hlimit

theorem extremizer_polynomial_degree (q : ℝ) (hq : 1 < q) (r : ℕ) (c : CoeffSpace r)
    (hc : c ∈ feasible q r) (hm : extrapolation r c = extremalValue q r) :
    (coefficientPolynomial c).natDegree = r := by
  obtain ⟨d, x, μ, hd, hdm, _, _, _, _, _, _, _, _, _, hdegree⟩ := finite_extremal_dual_complete q hq r
  rw [extremizer_unique q hq r c d hc hd hm hdm]
  exact hdegree

theorem envelope_minimizer_degree (q : ℝ) (hq : 1 < q) (r : ℕ) (p : ℝ[X])
    (hp : admissible r p) (hm : envelopeRatio q p = gamma q r) : p.natDegree = r := by
  have hd := extremizer_polynomial_degree q hq r (envelopeCandidate q r p)
    (envelopeCandidate_feasible q hq r hp) (envelopeCandidate_maximizes q hq r hp hm)
  rw [envelopeCandidate_polynomial q r hp.1, Polynomial.natDegree_smul p
    (ne_of_gt (div_pos (by norm_num) (envelope_width_pos q hq hp.2)))] at hd
  exact hd

end LocalCertification.Extremal
