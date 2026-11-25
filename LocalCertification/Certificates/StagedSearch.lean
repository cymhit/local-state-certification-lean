import LocalCertification.Certificates.CanonicalRawCheck

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates

/-- Numerator order -N,...,N; denominator order 1,...,N. Repetitions are retained. -/
def stagedRationals (N : ℕ) : List ℚ :=
  (List.range (2*N+1)).flatMap fun (a : ℕ) =>
    (List.range N).map fun (b : ℕ) => (((a : ℤ)-(N : ℤ) : ℤ) : ℚ) / ((b+1 : ℕ) : ℚ)

/-- Lexicographic Cartesian enumeration, with the first coordinate outermost. -/
def stagedArrays {α : Type} (s : List α) : (n : ℕ) → List (Fin n → α)
  | 0 => [Fin.elim0]
  | n+1 => s.flatMap fun a => (stagedArrays s n).map (Fin.cons a)

theorem mem_stagedArrays {α : Type} (s : List α) (n : ℕ) (f : Fin n → α) :
    f ∈ stagedArrays s n ↔ ∀ i, f i ∈ s := by
  induction n with
  | zero => simp [stagedArrays, Subsingleton.elim f Fin.elim0]
  | succ n ih =>
    simp only [stagedArrays, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a,ha,g,hg,rfl⟩ i
      refine Fin.cases ha (fun j => ?_) i
      exact (ih g).mp hg j
    · intro hf
      exact ⟨f 0,hf 0,Fin.tail f,(ih _).mpr (fun i => hf i.succ),Fin.cons_self_tail f⟩

theorem mem_stagedRationals (N : ℕ) (a : ℚ)
    (hn : a.num.natAbs ≤ N) (hd : a.den ≤ N) : a ∈ stagedRationals N := by
  have hn' : (a.num.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn
  have habs : |a.num| ≤ (N : ℤ) := by simpa using hn'
  have hlo := (abs_le.mp habs).1
  have hhi := (abs_le.mp habs).2
  have ha : ((a.num+(N : ℤ)).toNat : ℤ)=a.num+N := Int.toNat_of_nonneg (by omega)
  have hp := a.pos
  have hb : a.den-1+1=a.den := by omega
  simp only [stagedRationals,List.mem_flatMap,List.mem_range,List.mem_map]
  refine ⟨(a.num+(N : ℤ)).toNat,by omega,a.den-1,by omega,?_⟩
  rw [ha,hb]
  simpa using a.num_div_den

/-- Finite labels k denote the positive nodes k+1. Infinity is enumerated first. -/
def stagedNodes (r M : ℕ) : List (Fin (r+2) → Option ℕ) :=
  (stagedArrays (none :: (List.range M).map some) (r+2)).filter fun x =>
    decide ((∀ i j, i<j → canonicalNodeLt (x i) (x j)=true) ∧ x (Fin.last (r+1))=none)

/-- Stage N: M ascends from 1 to N, then nodes, coefficients, weights in Cartesian order.
The parity is fixed by r. No proof-carrying candidate is enumerated. -/
def stagedData (r N : ℕ) : List (CertificateData r) :=
  (List.range N).flatMap fun m =>
    (stagedNodes r (m+1)).flatMap fun x =>
      (stagedArrays (stagedRationals N) (r+1)).flatMap fun a =>
        (stagedArrays (stagedRationals N) (r+2)).map fun w =>
          (canonicalParity r,a,m+1,x,w)

theorem mem_stagedNodes (r M : ℕ) (x : Fin (r+2) → Option ℕ) :
    x ∈ stagedNodes r M ↔
      (∀ i, (x i).elim 0 (fun k => k+1)≤M) ∧
      (∀ i j, i<j → canonicalNodeLt (x i) (x j)=true) ∧ x (Fin.last (r+1))=none := by
  simp only [stagedNodes,List.mem_filter,decide_eq_true_eq,mem_stagedArrays]
  apply and_congr_left
  intro _
  apply forall_congr'
  intro i
  cases x i <;> simp

theorem stagedData_finite (r N : ℕ) : {d | d ∈ stagedData r N}.Finite := by
  exact List.finite_toSet _

theorem mem_stagedData (r N : ℕ) (d : CertificateData r) :
    d ∈ stagedData r N ↔
      d.1=canonicalParity r ∧ 1≤d.2.2.1 ∧ d.2.2.1≤N ∧
      d.2.2.2.1 ∈ stagedNodes r d.2.2.1 ∧
      (∀ i, d.2.1 i ∈ stagedRationals N) ∧
      (∀ i, d.2.2.2.2 i ∈ stagedRationals N) := by
  simp only [stagedData,List.mem_flatMap,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨m,hm,x,hx,a,ha,w,hw,rfl⟩
    exact ⟨rfl,by dsimp; omega,by dsimp; omega,hx,(mem_stagedArrays _ _ _).mp ha,
      (mem_stagedArrays _ _ _).mp hw⟩
  · rintro ⟨hh,hM,hN,hx,ha,hw⟩
    refine ⟨d.2.2.1-1,by omega,d.2.2.2.1,?_,d.2.1,
      (mem_stagedArrays _ _ _).mpr ha,d.2.2.2.2,(mem_stagedArrays _ _ _).mpr hw,?_⟩
    · simpa [Nat.sub_add_cancel hM] using hx
    · rw [Nat.sub_add_cancel hM,← hh]

/-- A concrete finite coverage bound, using reduced numerator magnitude and positive denominator. -/
def stagedDataBound (r : ℕ) (d : CertificateData r) : ℕ :=
  max d.2.2.1 (max
    (Finset.univ.sup fun i => max (d.2.1 i).num.natAbs (d.2.1 i).den)
    (Finset.univ.sup fun i => max (d.2.2.2.2 i).num.natAbs (d.2.2.2.2 i).den))

theorem stagedData_exhaustive (q : ℚ) (r : ℕ) (d : CertificateData r)
    (hd : canonicalRawCheck q r d=true) : d ∈ stagedData r (stagedDataBound r d) := by
  simp only [canonicalRawCheck,Bool.and_eq_true] at hd
  obtain ⟨hc,ht⟩ := hd
  have H := of_decide_eq_true hc
  obtain ⟨hM,hx,-,-⟩ := of_decide_eq_true ht
  apply (mem_stagedData _ _ _).mpr
  refine ⟨H.1,hM,le_max_left _ _,(mem_stagedNodes _ _ _).mpr ⟨hx,H.2.1,H.2.2.1⟩,?_,?_⟩
  · intro i
    have hi : max (d.2.1 i).num.natAbs (d.2.1 i).den ≤ stagedDataBound r d :=
      (Finset.le_sup (f:=fun i => max (d.2.1 i).num.natAbs (d.2.1 i).den)
        (Finset.mem_univ i)).trans ((le_max_left _ _).trans (le_max_right _ _))
    exact mem_stagedRationals _ _ ((le_max_left _ _).trans hi) ((le_max_right _ _).trans hi)
  · intro i
    have hi : max (d.2.2.2.2 i).num.natAbs (d.2.2.2.2 i).den ≤ stagedDataBound r d :=
      (Finset.le_sup (f:=fun i => max (d.2.2.2.2 i).num.natAbs (d.2.2.2.2 i).den)
        (Finset.mem_univ i)).trans ((le_max_right _ _).trans (le_max_right _ _))
    exact mem_stagedRationals _ _ ((le_max_left _ _).trans hi) ((le_max_right _ _).trans hi)

/-- A finite scan testing each candidate with the rational certificate checker. -/
def stagedFind (q : ℚ) (r N : ℕ) : Option (CertificateData r) :=
  (stagedData r N).find? (canonicalRawCheck q r)

theorem stagedFind_first (q : ℚ) (r N : ℕ) (d : CertificateData r)
    (hd : stagedFind q r N=some d) :
    canonicalRawCheck q r d=true ∧ ∃ before after,
      stagedData r N=before++d::after ∧ ∀ c ∈ before, canonicalRawCheck q r c=false := by
  simpa using List.find?_eq_some_iff_append.mp hd

theorem stagedFind_success_iff (q : ℚ) (r N : ℕ) :
    (stagedFind q r N).isSome=true ↔
      ∃ d ∈ stagedData r N, canonicalRawCheck q r d=true := by
  exact List.find?_isSome

theorem stagedFind_exists (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    ∃ N, (stagedFind q r N).isSome=true := by
  obtain ⟨d,hd⟩ := canonicalRawCheck_exists q hq r
  exact ⟨stagedDataBound r d,(stagedFind_success_iff _ _ _).mpr
    ⟨d,stagedData_exhaustive q r d hd,hd⟩⟩

/-- Executable increasing-stage search. Nat.find scans the decidable finite-stage predicate;
its existence proof is erased at runtime and does not choose the output certificate. -/
def stagedSearchIndex (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) : ℕ :=
  Nat.find (stagedFind_exists q hq r)

def stagedSearch (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) : CertificateData r :=
  (stagedFind q r (stagedSearchIndex q hq r)).getD default

theorem stagedSearch_terminates (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    stagedFind q r (stagedSearchIndex q hq r)=some (stagedSearch q hq r) := by
  have h := Nat.find_spec (stagedFind_exists q hq r)
  change (stagedFind q r (stagedSearchIndex q hq r)).isSome=true at h
  unfold stagedSearch
  cases he : stagedFind q r (stagedSearchIndex q hq r) <;> simp_all

theorem stagedSearchIndex_first (q : ℚ) (hq : 1<(q : ℝ)) (r N : ℕ)
    (hN : N<stagedSearchIndex q hq r) : stagedFind q r N=none := by
  have h := Nat.find_min (stagedFind_exists q hq r) hN
  cases he : stagedFind q r N <;> simp_all

theorem stagedSearchIndex_le (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) (d : CertificateData r)
    (hd : canonicalRawCheck q r d=true) : stagedSearchIndex q hq r≤stagedDataBound r d := by
  exact Nat.find_min' (stagedFind_exists q hq r)
    ((stagedFind_success_iff _ _ _).mpr ⟨d,stagedData_exhaustive q r d hd,hd⟩)

theorem stagedSearch_passes (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    canonicalRawCheck q r (stagedSearch q hq r)=true := by
  exact (stagedFind_first _ _ _ _ (stagedSearch_terminates q hq r)).1

theorem stagedSearch_correct (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    let d := stagedSearch q hq r
    let R := Polynomial.ofFn (r+1) d.2.1
    let p := ((R.eval 0)⁻¹ • R).map (Rat.castHom ℝ)
    ((∑ i, |d.2.2.2.2 i| : ℚ) : ℝ)=extremalValue (q : ℝ) r ∧
    gamma (q : ℝ) r=((2/(1+∑ i, |d.2.2.2.2 i|) : ℚ) : ℝ) ∧
    admissible r p ∧ envelopeRatio (q : ℝ) p=gamma (q : ℝ) r ∧
    ∀ P : ℝ[X], admissible r P → envelopeRatio (q : ℝ) P=gamma (q : ℝ) r → P=p := by
  exact canonicalRawCheck_optimality q hq r _ (stagedSearch_passes q hq r)

theorem stagedRationals_bounded (N : ℕ) (a : ℚ) (ha : a ∈ stagedRationals N) :
    ∃ (z : ℤ) (b : ℕ), |z|≤(N : ℤ) ∧ 0<b ∧ b≤N ∧ a=(z : ℚ)/(b : ℚ) := by
  simp only [stagedRationals,List.mem_flatMap,List.mem_map,List.mem_range] at ha
  obtain ⟨i,hi,j,hj,rfl⟩ := ha
  exact ⟨(i : ℤ)-N,j+1,abs_le.mpr ⟨by omega,by omega⟩,by omega,by omega,rfl⟩

theorem stagedData_canonical (q : ℚ) (r : ℕ) (c : CanonicalCandidate q r) (M : ℕ)
    (hc : c.canonicalCheck M) : c.data M ∈ stagedData r (stagedDataBound r (c.data M)) := by
  exact stagedData_exhaustive q r _ (canonicalRawCheck_complete q r c M hc)

theorem stagedData_zero (r : ℕ) : stagedData r 0=[] := by
  simp [stagedData]

/-- The finite data are returned together with a position in the selected finite list. -/
theorem stagedSearch_mem (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    stagedSearch q hq r ∈ stagedData r (stagedSearchIndex q hq r) := by
  exact List.mem_of_find?_eq_some (stagedSearch_terminates q hq r)

/-- Equality concerns the normalized optimizer only, with no claim about search order or timing. -/
theorem stagedSearch_same_optimizer (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    let R := Polynomial.ofFn (r+1) (stagedSearch q hq r).2.1
    let S := Polynomial.ofFn (r+1) (searchCertificate q hq r).2.1
    ((R.eval 0)⁻¹ • R).map (Rat.castHom ℝ)=((S.eval 0)⁻¹ • S).map (Rat.castHom ℝ) := by
  have h := stagedSearch_correct q hq r
  have hs := searchCertificate_correct q hq r
  exact (h.2.2.2.2 _ hs.2.2.2.2.1 hs.2.2.2.2.2.1).symm

/-- Exact rational value computed from the returned raw weights. -/
def stagedGamma (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) : ℚ :=
  2/(1+∑ i, |(stagedSearch q hq r).2.2.2.2 i|)

/-- Executable rational coefficient array of the normalized optimal polynomial. -/
def stagedPolynomial (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) : Fin (r+1) → ℚ :=
  let d := stagedSearch q hq r
  fun i => (arrayEval (r+1) d.2.1 0)⁻¹*d.2.1 i

theorem stagedPolynomial_eq (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    Polynomial.ofFn (r+1) (stagedPolynomial q hq r)=
      ((Polynomial.ofFn (r+1) (stagedSearch q hq r).2.1).eval 0)⁻¹ •
        Polynomial.ofFn (r+1) (stagedSearch q hq r).2.1 := by
  rw [← map_smul]
  congr 1
  funext i
  simp [stagedPolynomial,arrayEval_eq,smul_eq_mul]

/-- Both executable outputs denote the original exact value and unique normalized optimizer. -/
theorem stagedOutput_correct (q : ℚ) (hq : 1<(q : ℝ)) (r : ℕ) :
    let p := (Polynomial.ofFn (r+1) (stagedPolynomial q hq r)).map (Rat.castHom ℝ)
    (stagedGamma q hq r : ℝ)=gamma (q : ℝ) r ∧ admissible r p ∧
    envelopeRatio (q : ℝ) p=gamma (q : ℝ) r ∧
    ∀ P : ℝ[X], admissible r P → envelopeRatio (q : ℝ) P=gamma (q : ℝ) r → P=p := by
  dsimp only
  rw [stagedPolynomial_eq]
  have h := stagedSearch_correct q hq r
  exact ⟨h.2.1.symm,h.2.2⟩

end LocalCertification.Certificates
