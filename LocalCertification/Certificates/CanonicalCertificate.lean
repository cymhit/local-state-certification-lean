import LocalCertification.Certificates.CanonicalCandidate

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Certificates

theorem canonical_coefficients_smul_iff (a : ℚ) (ha : 0<a) (p : ℚ[X]) :
    coefficientsNonnegative (a • p) ↔ coefficientsNonnegative p := by
  constructor
  · intro h k _
    have hh := coefficientsNonnegative_all h k
    simpa only [Polynomial.coeff_smul, smul_eq_mul, mul_nonneg_iff_of_pos_left ha] using hh
  · intro h k _
    simpa only [Polynomial.coeff_smul, smul_eq_mul] using mul_nonneg ha.le (coefficientsNonnegative_all h k)

theorem canonical_tail_smul_iff (q a : ℚ) (ha : 0<a) (p : ℚ[X]) (M : ℕ) :
    tailCheck q (a • p) M ↔ tailCheck q p M := by
  have hs (P : ℚ[X]) : shiftedPolynomial (a • P) M=a • shiftedPolynomial P M := by
    simp [shiftedPolynomial, Polynomial.smul_eq_C_mul]
  have hd : weightedDifference q (a • p)=a • weightedDifference q p := by
    simp [weightedDifference, Polynomial.smul_eq_C_mul, mul_sub, mul_left_comm]
  simp only [tailCheck, hs, hd, canonical_coefficients_smul_iff a ha]

theorem canonical_coefficients_real_ray {p : ℚ[X]} (hp : coefficientsNonnegative p)
    {x : ℝ} (hx : 0≤x) : 0≤(p.map (Rat.castHom ℝ)).eval x := by
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (pow_nonneg hx k)
  rw [Polynomial.coeff_map]
  change (0 : ℝ)≤(p.coeff k : ℚ)
  exact_mod_cast coefficientsNonnegative_all hp k

theorem canonical_shifted_real_ray {p : ℚ[X]} {M : ℕ}
    (hp : coefficientsNonnegative (shiftedPolynomial p M))
    {x : ℝ} (hx : (M : ℝ)≤x) : 0≤(p.map (Rat.castHom ℝ)).eval x := by
  have h := canonical_coefficients_real_ray hp (sub_nonneg.mpr hx)
  simpa [shiftedPolynomial, Polynomial.map_comp, Polynomial.eval_comp] using h

namespace CanonicalCandidate
variable {q : ℚ} {r : ℕ}

theorem Q_positive_multiple (c : CanonicalCandidate q r) :
    c.Q=(c.R.eval 0)⁻¹ • ((-canonicalParity r) • c.R) := by
  have hh : -canonicalParity r=(-1 : ℚ)^r := by simp [canonicalParity,pow_succ]
  rw [hh, Q, p, smul_comm]

theorem tail_iff (c : CanonicalCandidate q r) (M : ℕ) :
    tailCheck q c.Q M ↔ tailCheck q ((-canonicalParity r) • c.R) M := by
  rw [c.Q_positive_multiple]
  exact canonical_tail_smul_iff q _ (inv_pos.mpr c.R_zero_pos) _ M

def data (c : CanonicalCandidate q r) (M : ℕ) : CertificateData r :=
  (canonicalParity r, Polynomial.toFn (r+1) c.R, M, c.x, c.ν)

def canonicalCheck (c : CanonicalCandidate q r) (M : ℕ) : Prop :=
  1≤M ∧ (∀ i (k : ℕ), c.x i=(k : OnePoint ℕ) → k+1≤M) ∧
  (∀ w ∈ Finset.Icc 1 M, |rationalCandidateValue q (canonicalParity r) c.R w|≤1) ∧
  tailCheck q c.Q M

theorem canonicalCheck_general (c : CanonicalCandidate q r) (M : ℕ)
    (hc : c.canonicalCheck M) : certificateCheck q r (c.data M)=true := by
  have hR : Polynomial.ofFn (r+1) (Polynomial.toFn (r+1) c.R)=c.R :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := c.degree; omega)
  unfold certificateCheck
  dsimp only [data]
  apply decide_eq_true
  refine ⟨by simp [canonicalParity],hc.1,?_,?_,c.mass,?_,?_⟩
  · apply arrayTailCheck_complete
    rw [oriented_ofFn,hR]
    exact (c.tail_iff M).mp hc.2.2.2
  · apply arrayPrefixCheck_complete
    simpa only [hR] using hc.2.2.1
  · intro j
    have heq (i : Fin (r+2)) := executableNodeMonomial_eq q j.val (show Option ℕ from c.x i)
    simp only [heq]
    exact c.moments j
  · change canonicalParity r+arrayEval (r+1) (Polynomial.toFn (r+1) c.R) 0=c.beta
    rw [arrayEval_eq,hR,c.R_zero]
    ring

/-- The canonical certificate determines exact B, gamma and the unique normalized extremal polynomial. -/
theorem optimality (c : CanonicalCandidate q r) (hq : 1<(q : ℝ)) (M : ℕ)
    (hc : c.canonicalCheck M) :
    (c.beta : ℝ)=extremalValue (q : ℝ) r ∧
    gamma (q : ℝ) r=((2/(1+c.beta) : ℚ) : ℝ) ∧
    admissible r (c.p.map (Rat.castHom ℝ)) ∧
    envelopeRatio (q : ℝ) (c.p.map (Rat.castHom ℝ))=gamma (q : ℝ) r ∧
    ∀ P : ℝ[X], admissible r P → envelopeRatio (q : ℝ) P=gamma (q : ℝ) r →
      P=c.p.map (Rat.castHom ℝ) := by
  have hR : Polynomial.ofFn (r+1) (Polynomial.toFn (r+1) c.R)=c.R :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := c.degree; omega)
  have hs := certificateCheck_sound q hq r (c.data M) (c.canonicalCheck_general M hc)
  change realCandidate r (canonicalParity r) _ ∈ _ ∧ _ at hs
  simp only [data,hR,arrayEval_eq] at hs
  have hn := rational_normalization_of_attainment q hq r (canonicalParity r) c.R c.degree hs.1 hs.2.1
  have he : extrapolation r (realCandidate r (canonicalParity r) c.R)=(c.beta : ℝ) := by
    rw [extrapolation_formula, realCandidate_polynomial r _ _ c.degree]
    have hv := ratPolynomial_eval_cast c.R 0
    simp only [Rat.cast_zero] at hv
    rw [hv,c.R_zero]
    simp [realCandidate]
  refine ⟨he.symm.trans hs.2.1,?_,hn.2⟩
  have hb : 1+canonicalParity r+c.R.eval 0=1+c.beta := by rw [c.R_zero]; ring
  simpa only [hb] using hs.2.2

theorem p_zero (c : CanonicalCandidate q r) : c.p.eval 0=1 := by
  simp [p,Polynomial.eval_smul,smul_eq_mul,inv_mul_cancel₀ (ne_of_gt c.R_zero_pos)]

theorem Q_degree (c : CanonicalCandidate q r) : c.Q.natDegree≤r := by
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_smul_le _ _).trans c.degree)

/-- A finite implementation of the canonical prefix and its two normalized shifted arrays. -/
def canonicalArrayCheck (c : CanonicalCandidate q r) (M : ℕ) : Bool :=
  decide (1≤M ∧ (∀ i, (c.x i).elim 0 (fun k => k+1)≤M) ∧
    arrayPrefixCheck q (canonicalParity r) (r+1) (Polynomial.toFn (r+1) c.R) M=true ∧
    arrayTailCheck q (r+1) (Polynomial.toFn (r+1) c.Q) M=true)

theorem canonicalArrayCheck_iff (c : CanonicalCandidate q r) (M : ℕ) :
    c.canonicalArrayCheck M=true ↔ c.canonicalCheck M := by
  have hR : Polynomial.ofFn (r+1) (Polynomial.toFn (r+1) c.R)=c.R :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := c.degree; omega)
  have hQ : Polynomial.ofFn (r+1) (Polynomial.toFn (r+1) c.Q)=c.Q :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := c.Q_degree; omega)
  constructor
  · intro hh
    obtain ⟨hM,hx,hP,hT⟩ := of_decide_eq_true hh
    refine ⟨hM,?_,?_,?_⟩
    · intro i k hik; have ht := hx i; simpa [hik] using ht
    · simpa only [hR] using arrayPrefixCheck_sound _ _ _ _ _ hP
    · simpa only [hQ] using arrayTailCheck_sound _ _ _ _ hT
  · rintro ⟨hM,hx,hP,hT⟩
    apply decide_eq_true
    refine ⟨hM,?_,?_,?_⟩
    · intro i
      cases hi : c.x i with
      | infty => exact Nat.zero_le _
      | coe k => exact hx i k hi
    · apply arrayPrefixCheck_complete
      simpa only [hR] using hP
    · apply arrayTailCheck_complete
      simpa only [hQ] using hT

theorem canonicalArrayCheck_general (c : CanonicalCandidate q r) (M : ℕ)
    (hc : c.canonicalArrayCheck M=true) : certificateCheck q r (c.data M)=true := by
  exact c.canonicalCheck_general M ((c.canonicalArrayCheck_iff M).mp hc)

/-- The normalized arrays certify the entire real ray, including the constant-tail case. -/
theorem canonical_real_ray (c : CanonicalCandidate q r) (M : ℕ)
    (hc : c.canonicalArrayCheck M=true) {x : ℝ} (hx : (M : ℝ)≤x) :
    0≤(c.Q.map (Rat.castHom ℝ)).eval x ∧
    0≤((weightedDifference q c.Q).map (Rat.castHom ℝ)).eval x := by
  have ht := ((c.canonicalArrayCheck_iff M).mp hc).2.2.2
  exact ⟨canonical_shifted_real_ray ht.1 hx,canonical_shifted_real_ray ht.2 hx⟩

/-- Integer tail monotonicity uses exactly the same normalized arrays. -/
theorem canonical_integer_tail (c : CanonicalCandidate q r) (hq : 0<q) (M : ℕ)
    (hc : c.canonicalArrayCheck M=true) (w : ℕ) (hw : M≤w) :
    0≤weightedPolynomial q c.Q w ∧
    weightedPolynomial q c.Q w≤weightedPolynomial q c.Q M := by
  exact tailCheck_bounds q hq c.Q M ((c.canonicalArrayCheck_iff M).mp hc).2.2.2 w hw

/-- Executable-array form of optimality, intended for stage-N search consumers. -/
theorem array_optimality (c : CanonicalCandidate q r) (hq : 1<(q : ℝ)) (M : ℕ)
    (hc : c.canonicalArrayCheck M=true) :
    (c.beta : ℝ)=extremalValue (q : ℝ) r ∧
    gamma (q : ℝ) r=((2/(1+c.beta) : ℚ) : ℝ) ∧
    admissible r (c.p.map (Rat.castHom ℝ)) ∧
    envelopeRatio (q : ℝ) (c.p.map (Rat.castHom ℝ))=gamma (q : ℝ) r ∧
    ∀ P : ℝ[X], admissible r P → envelopeRatio (q : ℝ) P=gamma (q : ℝ) r →
      P=c.p.map (Rat.castHom ℝ) := by
  exact c.optimality hq M ((c.canonicalArrayCheck_iff M).mp hc)

end CanonicalCandidate

/-- Every rational q>1 and every degree r, including r=0, admit a full canonical certificate. -/
theorem canonical_certificate_exists (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    ∃ (c : CanonicalCandidate q r) (M : ℕ), c.canonicalCheck M := by
  obtain ⟨d,x,μ,hd,hm,hx,ho,hi,hμ,he,hv,hs,hcontact,hlimit,hdegree⟩ :=
    finite_extremal_dual_complete (q : ℝ) hq r
  obtain ⟨a,b,hdb⟩ := extremizer_coefficients_rational q hq r d hd hm
  obtain ⟨ν,hν⟩ := rational_dual_weights q hq r x hx μ he
  let R := Polynomial.ofFn (r+1) b
  have hdeg : R.natDegree≤r := Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) b)
  have hR : R.map (Rat.castHom ℝ)=coefficientPolynomial d := by
    rw [hdb]; exact coefficientPolynomial_ratCast r a b
  have hlimit' : d.1=(canonicalParity r : ℝ) := by simpa [canonicalParity] using hlimit
  have ha : a=canonicalParity r := by
    have hh : (a : ℝ)=(canonicalParity r : ℝ) := by rw [← hlimit',hdb]
    exact_mod_cast hh
  have hrep : ∀ e : CoeffSpace r, extrapolation r e=
      ∑ i, (ν i : ℝ)*polynomialNode (q : ℝ) e.1 (coefficientPolynomial e) (x i) := by
    simpa only [hν] using he
  obtain ⟨hmass,hmom⟩ := rational_dual_finite_checks q r (r+2) x ν hrep
  let c : CanonicalCandidate q r :=
    ⟨x,ho,hi,R,hdeg,(by intro i; rw [hR,← hlimit']; exact hcontact i),ν,hmass,hmom,
      (by intro i; have ht := hs i; rw [← hν i] at ht; exact_mod_cast ht)⟩
  have hcd : realCandidate r (canonicalParity r) c.R=d := by
    rw [hdb]
    apply Prod.ext
    · change (canonicalParity r : ℝ)=(a : ℝ); rw [ha]
    · ext j
      simp [realCandidate,c,R,Polynomial.toFn,LinearMap.pi,j.isLt]
  have hfeas : realCandidate r (canonicalParity r) c.R ∈ feasible (q : ℝ) r := hcd ▸ hd
  have hqQ : 1<q := by exact_mod_cast hq
  have hlead := feasible_oriented_leading_positive q (by linarith) r (canonicalParity r)
    (by simp [canonicalParity]) c.R c.degree
    (by intro hz; have ht := c.R_zero_pos; rw [hz,Polynomial.eval_zero] at ht; exact lt_irrefl _ ht) hfeas
  let J := max 1 (Finset.univ.sup (fun i => (c.x i).elim 0 (fun k => k+1)))
  obtain ⟨M,hM,hT⟩ := exists_tailCheck_after q hqQ ((-canonicalParity r) • c.R) hlead J
  refine ⟨c,M,le_trans (le_max_left _ _) hM,?_,?_,(c.tail_iff M).mpr hT⟩
  · intro i k hik
    have hb : (c.x i).elim 0 (fun k => k+1)≤J :=
      le_trans (Finset.le_sup (f:=fun i => (c.x i).elim 0 (fun k => k+1)) (Finset.mem_univ i))
        (le_max_right _ _)
    have hk : k+1≤J := by simpa [hik] using hb
    exact hk.trans hM
  · intro w hw
    exact rationalCandidateValue_bound q r (canonicalParity r) c.R c.degree hfeas w
      (Finset.mem_Icc.mp hw).1

theorem canonical_array_certificate_exists (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    ∃ (c : CanonicalCandidate q r) (M : ℕ), c.canonicalArrayCheck M=true := by
  obtain ⟨c,M,hc⟩ := canonical_certificate_exists q hq r
  exact ⟨c,M,(c.canonicalArrayCheck_iff M).mpr hc⟩

end LocalCertification.Certificates
