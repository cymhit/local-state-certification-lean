import LocalCertification.Certificates.ExecutableTail
import LocalCertification.Certificates.Existence

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates

/-- Actual degree from finite rational data; trailing zeros and the zero array are handled explicitly. -/
def arrayDegree (N : ℕ) (a : Fin N → ℚ) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => a i≠0)).sup Fin.val

def arrayLeading (N : ℕ) (a : Fin N → ℚ) : ℚ :=
  if h : arrayDegree N a<N then a ⟨arrayDegree N a,h⟩ else 0

theorem arrayDegree_eq (N : ℕ) (a : Fin N → ℚ) :
    arrayDegree N a=(Polynomial.ofFn N a).natDegree := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hn : a i≠0 := (Finset.mem_filter.mp hi).2
    apply Polynomial.le_natDegree_of_ne_zero
    simpa [i.isLt] using hn
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    by_cases hkn : k<N
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt a hkn]
      by_contra hn
      have hb : k≤arrayDegree N a := Finset.le_sup (f:=Fin.val) (b:=⟨k,hkn⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
      omega
    · exact Polynomial.ofFn_coeff_eq_zero_of_ge a (le_of_not_gt hkn)

theorem arrayLeading_eq (N : ℕ) (a : Fin N → ℚ) :
    arrayLeading N a=(Polynomial.ofFn N a).leadingCoeff := by
  unfold arrayLeading
  rw [arrayDegree_eq]
  split_ifs with h
  · exact (Polynomial.ofFn_coeff_eq_val_of_lt a h).symm
  · exact (Polynomial.ofFn_coeff_eq_zero_of_ge a (le_of_not_gt h)).symm

theorem oriented_ofFn (N : ℕ) (a : Fin N → ℚ) (h : ℚ) :
    Polynomial.ofFn N (fun i => -h*a i)=(-h) • Polynomial.ofFn N a := by
  rw [← map_smul]
  rfl

theorem arrayPrefixCheck_complete (q h : ℚ) (N : ℕ) (a : Fin N → ℚ) (M : ℕ)
    (hp : ∀ w ∈ Finset.Icc 1 M, |rationalCandidateValue q h (Polynomial.ofFn N a) w|≤1) :
    arrayPrefixCheck q h N a M=true := by
  apply decide_eq_true
  intro w
  have h := hp (w.val+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  simpa only [arrayEval_eq, rationalCandidateValue, weightedPolynomial] using h

/-- A total executable candidate decision: zero numerator, positive-leading terminating tail search,
and genuine negative-leading rejection. No proposed truncation is assumed sufficient. -/
def candidateCheck (q : ℚ) (hq : 1<q) (r : ℕ) (h : ℚ) (a : Fin (r+1) → ℚ) : Bool :=
  if |h|=1 then
    if hz : arrayLeading (r+1) a=0 then true
    else if hp : 0<arrayLeading (r+1) (fun i => -h*a i) then
      arrayPrefixCheck q h (r+1) a
        (findTailShift q hq (r+1) (fun i => -h*a i) (by rw [← arrayLeading_eq]; exact hp) 1)
    else false
  else false

/-- Exact characterization of the full infinite constraints for any oriented candidate with |h|=1. -/
theorem candidateCheck_correct (q : ℚ) (hq : 1<q) (r : ℕ) (h : ℚ) (a : Fin (r+1) → ℚ)
    (hh : |h|=1) :
    candidateCheck q hq r h a=true ↔ realCandidate r h (Polynomial.ofFn (r+1) a) ∈ feasible (q : ℝ) r := by
  have hdeg : (Polynomial.ofFn (r+1) a).natDegree≤r :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) a)
  unfold candidateCheck
  rw [ite_eq_left hh]
  by_cases hz : arrayLeading (r+1) a=0
  · rw [dite_eq_left hz]
    have hpz : Polynomial.ofFn (r+1) a=0 := Polynomial.leadingCoeff_eq_zero.mp (by rwa [← arrayLeading_eq])
    constructor
    · intro _ x
      rw [realCandidate_polynomial r h _ hdeg,hpz,Polynomial.map_zero,polynomialNode_zero]
      change |(h : ℝ)|≤1
      exact_mod_cast hh.le
    · intro _; rfl
  · rw [dite_eq_right hz]
    by_cases hp : 0<arrayLeading (r+1) (fun i => -h*a i)
    · rw [dite_eq_left hp]
      let M := findTailShift q hq (r+1) (fun i => -h*a i) (by rw [← arrayLeading_eq]; exact hp) 1
      have hM := findTailShift_spec q hq (r+1) (fun i => -h*a i) (by rw [← arrayLeading_eq]; exact hp) 1
      constructor
      · intro hpass
        apply finite_rational_feasible q (by linarith) r h hh _ hdeg M hM.1
        · rw [← oriented_ofFn]
          exact arrayTailCheck_sound _ _ _ _ hM.2
        · exact arrayPrefixCheck_sound _ _ _ _ _ hpass
      · intro hf
        apply arrayPrefixCheck_complete
        intro w hw
        exact rationalCandidateValue_bound q r h _ hdeg hf w (Finset.mem_Icc.mp hw).1
    · rw [dite_eq_right hp]
      simp only [Bool.false_eq_true, false_iff]
      intro hf
      have hp0 : Polynomial.ofFn (r+1) a≠0 := by
        intro hz'
        apply hz
        rw [arrayLeading_eq,hz',Polynomial.leadingCoeff_zero]
      have hl := feasible_oriented_leading_positive q (by linarith) r h hh _ hdeg hp0 hf
      apply hp
      rwa [arrayLeading_eq,oriented_ofFn]

end LocalCertification.Certificates
