import LocalCertification.Certificates.CanonicalCertificate

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates

/-- Finite node order with infinity at the top; labels remain k ↔ k+1. -/
def canonicalNodeLt : Option ℕ → Option ℕ → Bool
  | some a, some b => decide (a<b)
  | some _, none => true
  | _, _ => false

def canonicalRawValue (q h : ℚ) (N : ℕ) (a : Fin N → ℚ) : Option ℕ → ℚ
  | none => h
  | some k => h+q⁻¹^(k+1)*arrayEval N a ((k+1 : ℕ) : ℚ)

/-- Only finite rational arithmetic and finite comparisons, before feasibility. -/
def canonicalRawCandidateCheck (q : ℚ) (r : ℕ) (d : CertificateData r) : Bool :=
  decide (d.1=canonicalParity r ∧
    (∀ i j : Fin (r+2), i<j → canonicalNodeLt (d.2.2.2.1 i) (d.2.2.2.1 j)=true) ∧
    d.2.2.2.1 (Fin.last (r+1))=none ∧
    (∀ i : Fin (r+2), canonicalRawValue q d.1 (r+1) d.2.1 (d.2.2.2.1 i)=(-1 : ℚ)^(i : ℕ)) ∧
    (∑ i, d.2.2.2.2 i)=1 ∧
    (∀ j : Fin (r+1), ∑ i, d.2.2.2.2 i*executableNodeMonomial q j.val (d.2.2.2.1 i)=(0 : ℚ)^j.val) ∧
    (∀ i : Fin (r+2), 0<(-1 : ℚ)^(i : ℕ)*d.2.2.2.2 i))

/-- Coefficients of Q = (-1)^r R/R(0), formed directly from the finite input array. -/
def canonicalRawQ (r : ℕ) (d : CertificateData r) : Fin (r+1) → ℚ :=
  fun i => (-1 : ℚ)^r*(arrayEval (r+1) d.2.1 0)⁻¹*d.2.1 i

/-- Computable canonical verifier on raw encodable data, suitable for stage-N lists. -/
def canonicalRawCheck (q : ℚ) (r : ℕ) (d : CertificateData r) : Bool :=
  canonicalRawCandidateCheck q r d && decide (1≤d.2.2.1 ∧
    (∀ i, (d.2.2.2.1 i).elim 0 (fun k => k+1)≤d.2.2.1) ∧
    arrayPrefixCheck q d.1 (r+1) d.2.1 d.2.2.1=true ∧
    arrayTailCheck q (r+1) (canonicalRawQ r d) d.2.2.1=true)

theorem canonicalNodeLt_sound (a b : Option ℕ) (h : canonicalNodeLt a b=true) :
    optionOrder (nodeToExtended (show OnePoint ℕ from a)) <
      optionOrder (nodeToExtended (show OnePoint ℕ from b)) := by
  cases a with
  | none => cases b <;> simp [canonicalNodeLt] at h
  | some a =>
    cases b with
    | none =>
      change (((a+1 : ℕ) : ℝ) : WithTop ℝ)<⊤
      simp
    | some b =>
      have hab : a<b := of_decide_eq_true h
      change (((a+1 : ℕ) : ℝ) : WithTop ℝ)<(((b+1 : ℕ) : ℝ) : WithTop ℝ)
      apply WithTop.coe_lt_coe.mpr
      exact_mod_cast Nat.add_lt_add_right hab 1

theorem canonicalNodeLt_complete (a b : Option ℕ)
    (h : optionOrder (nodeToExtended (show OnePoint ℕ from a)) <
      optionOrder (nodeToExtended (show OnePoint ℕ from b))) : canonicalNodeLt a b=true := by
  cases a with
  | none =>
    change (⊤ : WithTop ℝ)<_ at h
    exact (not_top_lt h).elim
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      apply decide_eq_true
      have hab : ((a+1 : ℕ) : ℝ)<((b+1 : ℕ) : ℝ) := WithTop.coe_lt_coe.mp h
      have hab' : a+1<b+1 := by exact_mod_cast hab
      omega

theorem canonicalRawValue_cast (q h : ℚ) (r : ℕ) (a : Fin (r+1) → ℚ) (x : Option ℕ) :
    (canonicalRawValue q h (r+1) a x : ℝ)=
      polynomialNode (q : ℝ) (h : ℝ) ((Polynomial.ofFn (r+1) a).map (Rat.castHom ℝ))
        (show OnePoint ℕ from x) := by
  cases x with
  | none => rfl
  | some k =>
    change _=polynomialNode (q : ℝ) (h : ℝ) ((Polynomial.ofFn (r+1) a).map (Rat.castHom ℝ)) (k : OnePoint ℕ)
    rw [polynomialNode_nat]
    simpa only [canonicalRawValue,arrayEval_eq,rationalCandidateValue,weightedPolynomial] using
      rationalCandidateValue_cast q h (Polynomial.ofFn (r+1) a) (k+1)

/-- Construct the proof-carrying candidate from checked raw data, with no classical choice. -/
def canonicalRawCandidate (q : ℚ) (r : ℕ) (d : CertificateData r)
    (hd : canonicalRawCandidateCheck q r d=true) : CanonicalCandidate q r := by
  have H := of_decide_eq_true hd
  refine ⟨(fun i => d.2.2.2.1 i),?_,H.2.2.1,Polynomial.ofFn (r+1) d.2.1,
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _),?_,d.2.2.2.2,H.2.2.2.2.1,?_,H.2.2.2.2.2.2⟩
  · intro i j hij
    exact canonicalNodeLt_sound _ _ (H.2.1 i j hij)
  · intro i
    rw [← H.1,← canonicalRawValue_cast,H.2.2.2.1]
    simp
  · intro j
    simpa only [← executableNodeMonomial_eq] using H.2.2.2.2.2.1 j

theorem canonicalRawQ_eq (q : ℚ) (r : ℕ) (d : CertificateData r)
    (hd : canonicalRawCandidateCheck q r d=true) :
    Polynomial.ofFn (r+1) (canonicalRawQ r d)=(canonicalRawCandidate q r d hd).Q := by
  change Polynomial.ofFn (r+1) (canonicalRawQ r d)=
    (-1 : ℚ)^r • ((Polynomial.ofFn (r+1) d.2.1).eval 0)⁻¹ • Polynomial.ofFn (r+1) d.2.1
  rw [← map_smul,← map_smul]
  congr 1
  funext i
  simp [canonicalRawQ,arrayEval_eq,smul_eq_mul,mul_assoc]

theorem canonicalRawCheck_sound (q : ℚ) (r : ℕ) (d : CertificateData r)
    (hd : canonicalRawCheck q r d=true) :
    ∃ hc : canonicalRawCandidateCheck q r d=true,
      (canonicalRawCandidate q r d hc).canonicalCheck d.2.2.1 := by
  simp only [canonicalRawCheck, Bool.and_eq_true] at hd
  obtain ⟨hcan,ht⟩ := hd
  obtain ⟨hM,hx,hP,hT⟩ := of_decide_eq_true ht
  have hh := (of_decide_eq_true hcan).1
  refine ⟨hcan,hM,?_,?_,?_⟩
  · intro i k hik
    have hb := hx i
    change d.2.2.2.1 i=some k at hik
    simpa [hik] using hb
  · have hb := arrayPrefixCheck_sound _ _ _ _ _ hP
    change ∀ w ∈ Finset.Icc 1 d.2.2.1, |rationalCandidateValue q (canonicalParity r) (Polynomial.ofFn (r+1) d.2.1) w|≤1
    simpa only [hh] using hb
  · rw [← canonicalRawQ_eq q r d hcan]
    exact arrayTailCheck_sound _ _ _ _ hT

theorem canonicalRawCheck_general (q : ℚ) (r : ℕ) (d : CertificateData r)
    (hd : canonicalRawCheck q r d=true) : certificateCheck q r d=true := by
  obtain ⟨hcan,hc⟩ := canonicalRawCheck_sound q r d hd
  have hh := (of_decide_eq_true hcan).1
  have he : (canonicalRawCandidate q r d hcan).data d.2.2.1=d := by
    apply Prod.ext
    · exact hh.symm
    · apply Prod.ext
      · ext i
        simp [CanonicalCandidate.data,canonicalRawCandidate,Polynomial.toFn,LinearMap.pi,i.isLt]
      · rfl
  rw [← he]
  exact (canonicalRawCandidate q r d hcan).canonicalCheck_general _ hc

theorem canonicalRawCheck_complete (q : ℚ) (r : ℕ) (c : CanonicalCandidate q r) (M : ℕ)
    (hc : c.canonicalCheck M) : canonicalRawCheck q r (c.data M)=true := by
  have hR : Polynomial.ofFn (r+1) (Polynomial.toFn (r+1) c.R)=c.R :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := c.degree; omega)
  have hcan : canonicalRawCandidateCheck q r (c.data M)=true := by
    apply decide_eq_true
    refine ⟨rfl,?_,c.infinity,?_,c.mass,?_,c.signs⟩
    · intro i j hij
      exact canonicalNodeLt_complete _ _ (c.ordered hij)
    · intro i
      have ht := canonicalRawValue_cast q (canonicalParity r) r (Polynomial.toFn (r+1) c.R)
        (show Option ℕ from c.x i)
      rw [hR,c.contact] at ht
      exact_mod_cast ht
    · intro j
      have heq (i : Fin (r+2)) := executableNodeMonomial_eq q j.val (show Option ℕ from c.x i)
      simpa only [CanonicalCandidate.data,heq] using c.moments j
  simp only [canonicalRawCheck,Bool.and_eq_true]
  refine ⟨hcan,?_⟩
  apply decide_eq_true
  refine ⟨hc.1,?_,?_,?_⟩
  · intro i
    change (c.x i).elim 0 (fun k => k+1)≤M
    cases hi : c.x i with
    | infty => exact Nat.zero_le _
    | coe k => exact hc.2.1 i k hi
  · apply arrayPrefixCheck_complete
    simpa only [CanonicalCandidate.data,hR] using hc.2.2.1
  · apply arrayTailCheck_complete
    rw [canonicalRawQ_eq q r (c.data M) hcan]
    change tailCheck q ((-1 : ℚ)^r • ((Polynomial.ofFn (r+1)
      (Polynomial.toFn (r+1) c.R)).eval 0)⁻¹ • Polynomial.ofFn (r+1) (Polynomial.toFn (r+1) c.R)) M
    rw [hR]
    exact hc.2.2.2

theorem canonicalRawCheck_exists (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    ∃ d : CertificateData r, canonicalRawCheck q r d=true := by
  obtain ⟨c,M,hc⟩ := canonical_certificate_exists q hq r
  exact ⟨c.data M,canonicalRawCheck_complete q r c M hc⟩

/-- Raw-data optimality: every passing finite record computes the original B, gamma and unique optimizer. -/
theorem canonicalRawCheck_optimality (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) (d : CertificateData r)
    (hd : canonicalRawCheck q r d=true) :
    let R := Polynomial.ofFn (r+1) d.2.1
    let p := ((R.eval 0)⁻¹ • R).map (Rat.castHom ℝ)
    ((∑ i, |d.2.2.2.2 i| : ℚ) : ℝ)=extremalValue (q : ℝ) r ∧
    gamma (q : ℝ) r=((2/(1+∑ i, |d.2.2.2.2 i|) : ℚ) : ℝ) ∧
    admissible r p ∧ envelopeRatio (q : ℝ) p=gamma (q : ℝ) r ∧
    ∀ P : ℝ[X], admissible r P → envelopeRatio (q : ℝ) P=gamma (q : ℝ) r → P=p := by
  obtain ⟨hcan,hc⟩ := canonicalRawCheck_sound q r d hd
  exact (canonicalRawCandidate q r d hcan).optimality hq d.2.2.1 hc

end LocalCertification.Certificates
