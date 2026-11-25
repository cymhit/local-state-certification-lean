import LocalCertification.Certificates.TailTermination

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Certificates

/-- Exact finite-node arithmetic, with label k representing the positive node k+1. -/
def rationalNodeMonomial (q : ℚ) (j : ℕ) (x : OnePoint ℕ) : ℚ :=
  x.elim 0 (fun k => q⁻¹^(k+1)*((k+1 : ℕ) : ℚ)^j)

theorem rationalNodeMonomial_cast (q : ℚ) (j : ℕ) (x : OnePoint ℕ) :
    (rationalNodeMonomial q j x : ℝ) = nodeMonomial (q : ℝ) j x := by
  induction x using OnePoint.rec with
  | infty => simp [rationalNodeMonomial, nodeMonomial]
  | coe k => simp [rationalNodeMonomial, nodeMonomial]

/-- A finite mass check and r+1 finite rational moments prove the full real extrapolation identity. -/
theorem finite_rational_reproduction (q : ℚ) (r n : ℕ)
    (x : Fin n → OnePoint ℕ) (μ : Fin n → ℚ)
    (hmass : ∑ i, μ i = 1)
    (hmom : ∀ j : Fin (r+1), ∑ i, μ i*rationalNodeMonomial q j.val (x i) = (0 : ℚ)^j.val)
    (c : CoeffSpace r) :
    extrapolation r c = ∑ i, (μ i : ℝ)*polynomialNode (q : ℝ) c.1 (coefficientPolynomial c) (x i) := by
  have hmassR : ∑ i, (μ i : ℝ) = 1 := by exact_mod_cast hmass
  have hmomR (j : Fin (r+1)) :
      ∑ i, (μ i : ℝ)*nodeMonomial (q : ℝ) j.val (x i) = (0 : ℝ)^j.val := by
    have h : ((∑ i, μ i*rationalNodeMonomial q j.val (x i) : ℚ) : ℝ) = ((0 : ℚ)^j.val : ℚ) :=
      congrArg (fun z : ℚ => (z : ℝ)) (hmom j)
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_zero, rationalNodeMonomial_cast] using h
  have hv : ∑ i, (μ i : ℝ) • evaluationDictionary (q : ℝ) r (x i) = extrapolationDictionary r := by
    apply Prod.ext
    · change (LinearMap.fst ℝ ℝ (Fin (r+1) → ℝ)) (∑ i, (μ i : ℝ) • evaluationDictionary (q : ℝ) r (x i)) = 1
      rw [map_sum]
      simpa [evaluationDictionary] using hmassR
    · change (LinearMap.snd ℝ ℝ (Fin (r+1) → ℝ)) (∑ i, (μ i : ℝ) • evaluationDictionary (q : ℝ) r (x i)) = (fun j => (0 : ℝ)^j.val)
      rw [map_sum]
      funext j
      simpa [evaluationDictionary] using hmomR j
  have h := congrArg (pairing c) hv
  simp only [map_sum, map_smul, smul_eq_mul, pairing_dictionary] at h
  rw [pairing_comm] at h
  exact h.symm

/-- The candidate polynomial is interpreted in the original real coefficient model. -/
def realCandidate (r : ℕ) (h : ℚ) (p : ℚ[X]) : CoeffSpace r :=
  ((h : ℝ), Polynomial.toFn (r+1) (p.map (Rat.castHom ℝ)))

theorem realCandidate_polynomial (r : ℕ) (h : ℚ) (p : ℚ[X]) (hp : p.natDegree≤r) :
    coefficientPolynomial (realCandidate r h p) = p.map (Rat.castHom ℝ) :=
  polynomial_reconstruction _ _ (Polynomial.natDegree_map_le.trans hp)

theorem ratPolynomial_eval_cast (p : ℚ[X]) (x : ℚ) :
    (p.map (Rat.castHom ℝ)).eval (x : ℝ) = ((p.eval x : ℚ) : ℝ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (Rat.castHom ℝ) x

def rationalCandidateValue (q h : ℚ) (p : ℚ[X]) (w : ℕ) : ℚ :=
  h + weightedPolynomial q p w

/-- Multiplying the paper's oriented polynomial by its positive normalization is unnecessary
for the sign arrays: here we orient the original numerator itself. -/
theorem rationalCandidateValue_oriented (q h : ℚ) (p : ℚ[X]) (hh : |h|=1) (w : ℕ) :
    rationalCandidateValue q h p w = orientedCandidateValue q h ((-h) • p) w := by
  have hh2 : h^2 = 1 := by nlinarith [sq_abs h]
  simp only [rationalCandidateValue, orientedCandidateValue, weightedPolynomial,
    Polynomial.eval_smul, smul_eq_mul]
  calc
    _ = h + h^2*(q⁻¹^w*p.eval (w : ℚ)) := by rw [hh2]; ring
    _ = _ := by ring

/-- Only finite exact prefix and coefficient tests are required to establish true infinite feasibility. -/
theorem finite_rational_feasible (q : ℚ) (hq : 0 < q) (r : ℕ) (h : ℚ) (hh : |h|=1)
    (p : ℚ[X]) (hp : p.natDegree≤r) (M : ℕ) (hM : 1≤M)
    (htail : tailCheck q ((-h) • p) M)
    (hprefix : ∀ w ∈ Finset.Icc 1 M, |rationalCandidateValue q h p w|≤1) :
    realCandidate r h p ∈ feasible (q : ℝ) r := by
  have hall := finite_prefix_tail_sound q hq h hh ((-h) • p) M hM htail
    (fun w hw => by rw [← rationalCandidateValue_oriented q h p hh]; exact hprefix w hw)
  intro x
  change |polynomialNode (q : ℝ) (h : ℝ) (coefficientPolynomial (realCandidate r h p)) x|≤1
  rw [realCandidate_polynomial r h p hp]
  induction x using OnePoint.rec with
  | infty => simpa using (show |(h : ℝ)|≤1 by exact_mod_cast hh.le)
  | coe k =>
    have hk := hall (k+1) (by omega)
    rw [← rationalCandidateValue_oriented q h p hh] at hk
    have he : polynomialNode (q : ℝ) (h : ℝ) (p.map (Rat.castHom ℝ)) (k : OnePoint ℕ) =
        (rationalCandidateValue q h p (k+1) : ℝ) := by
      rw [polynomialNode_nat]
      have hev := ratPolynomial_eval_cast p ((k+1 : ℕ) : ℚ)
      simp only [Rat.cast_natCast] at hev
      rw [hev]
      simp [rationalCandidateValue, weightedPolynomial]
    rw [he]
    exact_mod_cast hk

/-- The finite rational dual test bounds every feasible function, not merely the reconstructed candidate. -/
theorem finite_rational_dual_bound (q : ℚ) (r n : ℕ)
    (x : Fin n → OnePoint ℕ) (μ : Fin n → ℚ)
    (hmass : ∑ i, μ i = 1)
    (hmom : ∀ j : Fin (r+1), ∑ i, μ i*rationalNodeMonomial q j.val (x i) = (0 : ℚ)^j.val)
    (c : CoeffSpace r) (hc : c ∈ feasible (q : ℝ) r) :
    extrapolation r c ≤ ((∑ i, |μ i| : ℚ) : ℝ) := by
  rw [finite_rational_reproduction q r n x μ hmass hmom, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Rat.cast_abs]
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hc (x i)))

/-- A passing finite rational certificate attains the original B and computes its original gamma. -/
theorem finite_rational_certificate_optimal (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ)
    (h : ℚ) (hh : |h|=1) (p : ℚ[X]) (hp : p.natDegree≤r)
    (M : ℕ) (hM : 1≤M) (htail : tailCheck q ((-h) • p) M)
    (hprefix : ∀ w ∈ Finset.Icc 1 M, |rationalCandidateValue q h p w|≤1)
    (n : ℕ) (x : Fin n → OnePoint ℕ) (μ : Fin n → ℚ)
    (hmass : ∑ i, μ i = 1)
    (hmom : ∀ j : Fin (r+1), ∑ i, μ i*rationalNodeMonomial q j.val (x i) = (0 : ℚ)^j.val)
    (hnorm : h+p.eval 0 = ∑ i, |μ i|) :
    realCandidate r h p ∈ feasible (q : ℝ) r ∧
    extrapolation r (realCandidate r h p) = extremalValue (q : ℝ) r ∧
    gamma (q : ℝ) r = ((2/(1+h+p.eval 0) : ℚ) : ℝ) := by
  have hq0 : 0 < q := by exact_mod_cast (lt_trans zero_lt_one hq)
  have hc := finite_rational_feasible q hq0 r h hh p hp M hM htail hprefix
  have he : extrapolation r (realCandidate r h p) = ((h+p.eval 0 : ℚ) : ℝ) := by
    rw [extrapolation_formula, realCandidate_polynomial r h p hp]
    have hv := ratPolynomial_eval_cast p 0
    simpa only [Rat.cast_zero, Rat.cast_add, realCandidate] using congrArg (fun z : ℝ => (h : ℝ)+z) hv
  have hm : extrapolation r (realCandidate r h p) = extremalValue (q : ℝ) r := by
    apply le_antisymm (extrapolation_le_extremalValue (q : ℝ) hq r hc)
    obtain ⟨c,hc',hmax⟩ := extremalValue_attained (q : ℝ) hq r
    rw [he, hnorm, ← hmax]
    exact finite_rational_dual_bound q r n x μ hmass hmom c hc'
  refine ⟨hc,hm,?_⟩
  rw [gamma_eq_extremalValue (q : ℝ) hq r, ← hm, he]
  push_cast
  congr 1
  ring

/-- Actual attainment identifies the normalized rational numerator with the unique original optimizer. -/
theorem rational_normalization_of_attainment (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ)
    (h : ℚ) (p : ℚ[X]) (hp : p.natDegree≤r)
    (hc : realCandidate r h p ∈ feasible (q : ℝ) r)
    (hm : extrapolation r (realCandidate r h p) = extremalValue (q : ℝ) r) :
    0 < p.eval 0 ∧
      admissible r (((p.eval 0)⁻¹ • p).map (Rat.castHom ℝ)) ∧
      envelopeRatio (q : ℝ) (((p.eval 0)⁻¹ • p).map (Rat.castHom ℝ)) = gamma (q : ℝ) r ∧
      ∀ P : ℝ[X], admissible r P → envelopeRatio (q : ℝ) P = gamma (q : ℝ) r →
        P = ((p.eval 0)⁻¹ • p).map (Rat.castHom ℝ) := by
  have hv : extremalValue (q : ℝ) r - (h : ℝ) = ((p.eval 0 : ℚ) : ℝ) := by
    rw [← hm, extrapolation_formula, realCandidate_polynomial r h p hp]
    have he := ratPolynomial_eval_cast p 0
    simp only [Rat.cast_zero] at he
    rw [he]
    change (h : ℝ)+(p.eval 0 : ℚ)-(h : ℝ) = _
    ring
  have hposR := extremizer_denominator_pos (q : ℝ) hq r hc
  change 0 < extremalValue (q : ℝ) r - (h : ℝ) at hposR
  rw [hv] at hposR
  have hpos : 0 < p.eval 0 := by exact_mod_cast hposR
  have he : ((p.eval 0)⁻¹ • p).map (Rat.castHom ℝ) =
      extremizerPolynomial (q : ℝ) r (realCandidate r h p) := by
    rw [extremizerPolynomial, realCandidate_polynomial r h p hp]
    change ((p.eval 0)⁻¹ • p).map (Rat.castHom ℝ) =
      (extremalValue (q : ℝ) r - (h : ℝ))⁻¹ • p.map (Rat.castHom ℝ)
    rw [hv]
    simp only [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C,
      Rat.coe_castHom, Rat.cast_inv]
  have ha := extremizerPolynomial_admissible (q : ℝ) hq r hc hm
  have hr : envelopeRatio (q : ℝ) (extremizerPolynomial (q : ℝ) r (realCandidate r h p)) =
      gamma (q : ℝ) r := by
    rw [gamma_eq_extremalValue (q : ℝ) hq r]
    exact le_antisymm (extremizerPolynomial_ratio_le (q : ℝ) hq r hc)
      (envelopeRatio_lower (q : ℝ) hq r ha)
  rw [← he] at ha hr
  exact ⟨hpos,ha,hr,fun P hP hmP => envelope_minimizer_unique (q : ℝ) hq r P _ hP ha hmP hr⟩

end LocalCertification.Certificates
