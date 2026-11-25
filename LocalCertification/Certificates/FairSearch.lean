import LocalCertification.Certificates.CandidateDecision
import Mathlib.Logic.Encodable.Pi

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates

/-- Finite certificate data. Every array has fixed length; a finite node k denotes k+1, none denotes infinity. -/
abbrev CertificateData (r : ℕ) :=
  ℚ × (Fin (r+1) → ℚ) × ℕ × (Fin (r+2) → Option ℕ) × (Fin (r+2) → ℚ)

def executableNodeMonomial (q : ℚ) (j : ℕ) (x : Option ℕ) : ℚ :=
  match x with
  | none => 0
  | some k => q⁻¹^(k+1)*((k+1 : ℕ) : ℚ)^j

theorem executableNodeMonomial_eq (q : ℚ) (j : ℕ) (x : Option ℕ) :
    executableNodeMonomial q j x = rationalNodeMonomial q j (show OnePoint ℕ from x) := by
  cases x <;> rfl

/-- Entirely finite rational certificate verification, including the true dual mass, moments and norm equality. -/
def certificateCheck (q : ℚ) (r : ℕ) (c : CertificateData r) : Bool :=
  decide (|c.1|=1 ∧ 1≤c.2.2.1 ∧
    arrayTailCheck q (r+1) (fun i => -c.1*c.2.1 i) c.2.2.1=true ∧
    arrayPrefixCheck q c.1 (r+1) c.2.1 c.2.2.1=true ∧
    (∑ i, c.2.2.2.2 i)=1 ∧
    (∀ j : Fin (r+1), ∑ i, c.2.2.2.2 i*executableNodeMonomial q j.val (c.2.2.2.1 i)=(0 : ℚ)^j.val) ∧
    c.1+arrayEval (r+1) c.2.1 0=∑ i, |c.2.2.2.2 i|)

/-- A successful executable certificate computes the original B and gamma; no infinite condition is an input. -/
theorem certificateCheck_sound (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) (c : CertificateData r)
    (hc : certificateCheck q r c=true) :
    realCandidate r c.1 (Polynomial.ofFn (r+1) c.2.1) ∈ feasible (q : ℝ) r ∧
    extrapolation r (realCandidate r c.1 (Polynomial.ofFn (r+1) c.2.1))=extremalValue (q : ℝ) r ∧
    gamma (q : ℝ) r=((2/(1+c.1+arrayEval (r+1) c.2.1 0) : ℚ) : ℝ) := by
  obtain ⟨hh,hM,hT,hP,hmass,hmom,hnorm⟩ := of_decide_eq_true hc
  have hdeg : (Polynomial.ofFn (r+1) c.2.1).natDegree≤r :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
  have htail : tailCheck q ((-c.1) • Polynomial.ofFn (r+1) c.2.1) c.2.2.1 := by
    rw [← oriented_ofFn]
    exact arrayTailCheck_sound _ _ _ _ hT
  have h := finite_rational_certificate_optimal q hq r c.1 hh _ hdeg c.2.2.1 hM htail
    (arrayPrefixCheck_sound _ _ _ _ _ hP) (r+2) (fun i => c.2.2.2.1 i) c.2.2.2.2 hmass
    (by simpa only [← executableNodeMonomial_eq] using hmom)
    (by simpa only [arrayEval_eq] using hnorm)
  simpa only [arrayEval_eq] using h

/-- Completeness: every rational base q>1 and degree r admit a passing finite executable certificate. -/
theorem certificateCheck_exists (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    ∃ c : CertificateData r, certificateCheck q r c=true := by
  obtain ⟨h,p,M,x,ν,_hsign,hh,hp,_hp0,hM,hT,hP,_hx,_ho,_hi,_hν,hmass,hmom,hnorm,_hsg,_hf,_hm⟩ :=
    finite_rational_certificate_exists q hq r
  let a := Polynomial.toFn (r+1) p
  have ha : Polynomial.ofFn (r+1) a=p := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  refine ⟨(h,a,M,x,ν),?_⟩
  apply decide_eq_true
  refine ⟨hh,hM,?_,?_,hmass,?_,?_⟩
  · apply arrayTailCheck_complete
    rw [oriented_ofFn,ha]
    exact hT
  · apply arrayPrefixCheck_complete
    simpa only [ha] using hP
  · intro j
    have heq (i : Fin (r+2)) := executableNodeMonomial_eq q j.val (show Option ℕ from x i)
    simp only [heq]
    exact hmom j
  · simpa only [arrayEval_eq,ha] using hnorm

/-- The explicit degree-zero certificate is tested first; all other finite data remain in the fair enumeration. -/
def seedCertificate (q : ℚ) (r : ℕ) : CertificateData r :=
  (-1, (fun i => if i.val=0 then 2*q else 0), 1,
    (fun i => if i.val=0 then some 0 else none),
    (fun i => if i.val=0 then q else if i.val=1 then 1-q else 0))

/-- One inexpensive seed followed by all finite rational data, with finite work at each index. -/
def decodeCertificate (q : ℚ) (r k : ℕ) : Option (CertificateData r) :=
  match k with
  | 0 => some (seedCertificate q r)
  | k+1 => Encodable.decode k

def certificateAt (q : ℚ) (r k : ℕ) : Bool :=
  match decodeCertificate q r k with
  | none => false
  | some c => certificateCheck q r c

/-- Every concrete certificate is visited at its finite encoding index. -/
theorem certificateAt_fair (q : ℚ) (r : ℕ) (c : CertificateData r) :
    certificateAt q r (Encodable.encode c+1)=certificateCheck q r c := by
  simp only [certificateAt,decodeCertificate,Encodable.encodek]

theorem certificateAt_exists (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    ∃ k : ℕ, certificateAt q r k=true := by
  obtain ⟨c,hc⟩ := certificateCheck_exists q hq r
  exact ⟨Encodable.encode c+1,by rwa [certificateAt_fair]⟩

/-- Executable fair global search. Its termination follows from the general all-degree existence theorem. -/
def searchCertificateIndex (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) : ℕ :=
  Nat.find (certificateAt_exists q hq r)

def searchCertificate (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) : CertificateData r :=
  (decodeCertificate q r (searchCertificateIndex q hq r)).getD default

theorem searchCertificate_passes (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    certificateCheck q r (searchCertificate q hq r)=true := by
  have h := Nat.find_spec (certificateAt_exists q hq r)
  change certificateAt q r (searchCertificateIndex q hq r)=true at h
  unfold searchCertificate certificateAt at *
  cases he : decodeCertificate q r (searchCertificateIndex q hq r) with
  | none => simp [he] at h
  | some c => simpa only [he,Option.getD_some] using h

/-- Any known certificate gives a finite bound on the fair search index; this is not a uniform complexity bound. -/
theorem searchCertificateIndex_le (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) (c : CertificateData r)
    (hc : certificateCheck q r c=true) : searchCertificateIndex q hq r≤Encodable.encode c+1 :=
  Nat.find_min' (certificateAt_exists q hq r) (by rwa [certificateAt_fair])

/-- The search returns the unique original optimizer and its original exact gamma, for every degree. -/
theorem searchCertificate_correct (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    let c := searchCertificate q hq r
    let p := Polynomial.ofFn (r+1) c.2.1
    realCandidate r c.1 p ∈ feasible (q : ℝ) r ∧
    extrapolation r (realCandidate r c.1 p)=extremalValue (q : ℝ) r ∧
    gamma (q : ℝ) r=((2/(1+c.1+arrayEval (r+1) c.2.1 0) : ℚ) : ℝ) ∧
    0<p.eval 0 ∧ admissible r (((p.eval 0)⁻¹ • p).map (Rat.castHom ℝ)) ∧
    envelopeRatio (q : ℝ) (((p.eval 0)⁻¹ • p).map (Rat.castHom ℝ))=gamma (q : ℝ) r ∧
    ∀ P : ℝ[X], admissible r P → envelopeRatio (q : ℝ) P=gamma (q : ℝ) r →
      P=((p.eval 0)⁻¹ • p).map (Rat.castHom ℝ) := by
  dsimp only
  have h := certificateCheck_sound q hq r _ (searchCertificate_passes q hq r)
  exact ⟨h.1,h.2.1,h.2.2,rational_normalization_of_attainment q hq r _ _
    (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)) h.1 h.2.1⟩

end LocalCertification.Certificates
