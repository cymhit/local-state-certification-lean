import LocalCertification.Certificates.RationalDual

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Certificates

theorem rationalCandidateValue_cast (q h : ℚ) (p : ℚ[X]) (w : ℕ) :
    (rationalCandidateValue q h p w : ℝ) =
      (h : ℝ)+(q : ℝ)⁻¹^w*(p.map (Rat.castHom ℝ)).eval (w : ℝ) := by
  have he := ratPolynomial_eval_cast p (w : ℚ)
  simp only [Rat.cast_natCast] at he
  rw [he]
  simp [rationalCandidateValue, weightedPolynomial]

/-- True infinite feasibility entails the exact rational finite-prefix inequalities at every positive node. -/
theorem rationalCandidateValue_bound (q : ℚ) (r : ℕ) (h : ℚ) (p : ℚ[X])
    (hp : p.natDegree≤r) (hc : realCandidate r h p ∈ feasible (q : ℝ) r)
    (w : ℕ) (hw : 1≤w) : |rationalCandidateValue q h p w|≤1 := by
  have he : w-1+1=w := by omega
  have hb := hc ((w-1 : ℕ) : OnePoint ℕ)
  rw [realCandidate_polynomial r h p hp, polynomialNode_nat, he] at hb
  change |(h : ℝ)+(q : ℝ)⁻¹^w*(p.map (Rat.castHom ℝ)).eval (w : ℝ)|≤1 at hb
  rw [← rationalCandidateValue_cast] at hb
  exact_mod_cast hb

/-- A nonzero feasible numerator has positive oriented leading coefficient; a negative one violates actual constraints. -/
theorem feasible_oriented_leading_positive (q : ℚ) (hq : 0<q) (r : ℕ)
    (h : ℚ) (hh : |h|=1) (p : ℚ[X]) (hp : p.natDegree≤r) (hp0 : p≠0)
    (hc : realCandidate r h p ∈ feasible (q : ℝ) r) : 0 < ((-h) • p).leadingCoeff := by
  have hh0 : h≠0 := by intro hz; simp [hz] at hh
  have hn : ((-h) • p : ℚ[X])≠0 := smul_ne_zero (neg_ne_zero.mpr hh0) hp0
  have hlc : ((-h) • p).leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr hn
  by_contra hnot
  have hneg : ((-h) • p).leadingCoeff<0 := lt_of_le_of_ne (le_of_not_gt hnot) hlc
  obtain ⟨w,hw,hbad⟩ := negative_leading_rejected q hq h hh ((-h) • p) hneg 1
  rw [← rationalCandidateValue_oriented q h p hh] at hbad
  exact not_lt_of_ge (rationalCandidateValue_bound q r h p hp hc w hw) hbad

/-- Every degree has an actual finite rational optimal certificate, with original ordered r+2 support including infinity. -/
theorem finite_rational_certificate_exists (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ) :
    ∃ (h : ℚ) (p : ℚ[X]) (M : ℕ) (x : Fin (r+2) → OnePoint ℕ) (ν : Fin (r+2) → ℚ),
      h=(-1 : ℚ)^(r+1) ∧ |h|=1 ∧ p.natDegree≤r ∧ 0<p.eval 0 ∧ 1≤M ∧
      tailCheck q ((-h) • p) M ∧
      (∀ w ∈ Finset.Icc 1 M, |rationalCandidateValue q h p w|≤1) ∧
      Function.Injective x ∧ OrderedExtendedNodes (fun i => nodeToExtended (x i)) ∧
      x (Fin.last (r+1))=∞ ∧ (∀ i, ν i≠0) ∧
      (∑ i, ν i=1) ∧
      (∀ j : Fin (r+1), ∑ i, ν i*rationalNodeMonomial q j.val (x i)=(0 : ℚ)^j.val) ∧
      h+p.eval 0=∑ i, |ν i| ∧
      (∀ i : Fin (r+2), 0<(-1 : ℚ)^(i : ℕ)*ν i) ∧
      realCandidate r h p ∈ feasible (q : ℝ) r ∧
      extrapolation r (realCandidate r h p)=extremalValue (q : ℝ) r := by
  obtain ⟨c,x,μ,hc,hm,hx,ho,hi,hμ,he,hv,hs,hcontact,hlimit,hdegree⟩ :=
    finite_extremal_dual_complete (q : ℝ) hq r
  obtain ⟨a,b,hcb⟩ := extremizer_coefficients_rational q hq r c hc hm
  obtain ⟨ν,hν⟩ := rational_dual_weights q hq r x hx μ he
  let p := Polynomial.ofFn (r+1) b
  have hp : p.natDegree≤r := Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) b)
  have hcp : realCandidate r a p=c := by
    rw [hcb]
    apply Prod.ext
    · rfl
    · ext j
      simp [realCandidate, p, Polynomial.toFn, LinearMap.pi, j.isLt]
  have hsign : a=(-1 : ℚ)^(r+1) := by
    have hh := congrArg Prod.fst hcb
    change c.1=(a : ℝ) at hh
    rw [hlimit] at hh
    exact_mod_cast hh.symm
  have ha : |a|=1 := by rw [hsign]; simp
  have hfeas : realCandidate r a p ∈ feasible (q : ℝ) r := hcp ▸ hc
  have hmax : extrapolation r (realCandidate r a p)=extremalValue (q : ℝ) r := by rw [hcp]; exact hm
  have hp0 := (rational_normalization_of_attainment q hq r a p hp hfeas hmax).1
  have hpn : p≠0 := by intro hz; simp [hz] at hp0
  have hqR : 1<q := by exact_mod_cast hq
  have hlead := feasible_oriented_leading_positive q (by linarith) r a ha p hp hpn hfeas
  obtain ⟨M,hM,hT⟩ := exists_tailCheck_after q hqR ((-a) • p) hlead 1
  have heν : ∀ c' : CoeffSpace r, extrapolation r c' =
      ∑ i, (ν i : ℝ)*polynomialNode (q : ℝ) c'.1 (coefficientPolynomial c') (x i) := by
    simpa only [hν] using he
  obtain ⟨hνmass,hνmom⟩ := rational_dual_finite_checks q r (r+2) x ν heν
  have hnorm : a+p.eval 0=∑ i, |ν i| := by
    have heval : extrapolation r (realCandidate r a p)=((a+p.eval 0 : ℚ) : ℝ) := by
      rw [extrapolation_formula, realCandidate_polynomial r a p hp]
      have h := ratPolynomial_eval_cast p 0
      simpa only [realCandidate, Rat.cast_zero, Rat.cast_add] using congrArg (fun z : ℝ => (a : ℝ)+z) h
    have htv : ∑ i, |(ν i : ℝ)|=extremalValue (q : ℝ) r := by simpa only [hν] using hv
    have h := heval.symm.trans (hmax.trans htv.symm)
    exact_mod_cast h
  refine ⟨a,p,M,x,ν,hsign,ha,hp,hp0,hM,hT,?_,hx,ho,hi,?_,hνmass,hνmom,hnorm,?_,hfeas,hmax⟩
  · intro w hw
    exact rationalCandidateValue_bound q r a p hp hfeas w (Finset.mem_Icc.mp hw).1
  · intro i hz
    have hh := hν i
    rw [hz,Rat.cast_zero] at hh
    exact hμ i hh.symm
  · intro i
    have h := hs i
    rw [← hν i] at h
    exact_mod_cast h

end LocalCertification.Certificates
