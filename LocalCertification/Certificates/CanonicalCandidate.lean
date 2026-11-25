import LocalCertification.Certificates.FairSearch

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Certificates

def canonicalParity (r : ℕ) : ℚ := (-1 : ℚ)^(r+1)

/-- Canonical interpolation data, before any feasibility or optimality assertion.
Finite label k represents the positive integer k+1; none is infinity. -/
structure CanonicalCandidate (q : ℚ) (r : ℕ) where
  x : Fin (r+2) → OnePoint ℕ
  ordered : OrderedExtendedNodes (fun i => nodeToExtended (x i))
  infinity : x (Fin.last (r+1)) = ∞
  R : ℚ[X]
  degree : R.natDegree ≤ r
  contact : ∀ i, polynomialNode (q : ℝ) (canonicalParity r : ℝ)
    (R.map (Rat.castHom ℝ)) (x i) = (-1 : ℝ)^(i : ℕ)
  ν : Fin (r+2) → ℚ
  mass : ∑ i, ν i = 1
  moments : ∀ j : Fin (r+1), ∑ i, ν i*rationalNodeMonomial q j.val (x i) = (0 : ℚ)^j.val
  signs : ∀ i : Fin (r+2), 0 < (-1 : ℚ)^(i : ℕ)*ν i

namespace CanonicalCandidate
variable {q : ℚ} {r : ℕ}
def beta (c : CanonicalCandidate q r) : ℚ := ∑ i, |c.ν i|
def p (c : CanonicalCandidate q r) : ℚ[X] := (c.R.eval 0)⁻¹ • c.R
def Q (c : CanonicalCandidate q r) : ℚ[X] := (-1 : ℚ)^r • c.p

theorem beta_gt_one (c : CanonicalCandidate q r) : 1 < c.beta := by
  have hn := c.signs (⟨1, by omega⟩ : Fin (r+2))
  have hn' : c.ν ⟨1, by omega⟩ < 0 := by simpa using hn
  have hlt : ∑ i, c.ν i < ∑ i, |c.ν i| := by
    apply Finset.sum_lt_sum
    · intro i _; exact le_abs_self _
    · exact ⟨⟨1, by omega⟩, Finset.mem_univ _, by rw [abs_of_neg hn']; linarith⟩
  simpa [c.mass, beta] using hlt

theorem R_zero (c : CanonicalCandidate q r) : c.R.eval 0 = c.beta-canonicalParity r := by
  have hrep := finite_rational_reproduction q r (r+2) c.x c.ν c.mass c.moments
    (realCandidate r (canonicalParity r) c.R)
  rw [extrapolation_formula, realCandidate_polynomial r _ _ c.degree] at hrep
  have hc (i : Fin (r+2)) :
      (c.ν i : ℝ)*polynomialNode (q : ℝ) (canonicalParity r : ℝ)
        (c.R.map (Rat.castHom ℝ)) (c.x i) = (|c.ν i| : ℚ) := by
    rw [c.contact]
    have ha : |c.ν i| = (-1 : ℚ)^(i : ℕ)*c.ν i := by
      calc
        _ = |(-1 : ℚ)^(i : ℕ)*c.ν i| := by simp
        _ = _ := abs_of_pos (c.signs i)
    rw [ha]
    push_cast
    ring
  change (canonicalParity r : ℝ)+(c.R.map (Rat.castHom ℝ)).eval 0 = _ at hrep
  change (canonicalParity r : ℝ)+(c.R.map (Rat.castHom ℝ)).eval 0 = ∑ i, (c.ν i : ℝ)*polynomialNode (q : ℝ) (canonicalParity r : ℝ) (c.R.map (Rat.castHom ℝ)) (c.x i) at hrep
  simp only [hc] at hrep
  rw [← Rat.cast_zero, ratPolynomial_eval_cast] at hrep
  have he : canonicalParity r+c.R.eval 0=c.beta := by exact_mod_cast hrep
  linarith

theorem R_zero_pos (c : CanonicalCandidate q r) : 0 < c.R.eval 0 := by
  have hh : canonicalParity r ≤ 1 := by
    have ha : |canonicalParity r|=1 := by simp [canonicalParity]
    exact (le_abs_self _).trans ha.le
  rw [c.R_zero]
  linarith [c.beta_gt_one]

end CanonicalCandidate

theorem canonicalCandidate_exists (q : ℚ) (hq : 1 < (q : ℝ)) (r : ℕ)
    (x : Fin (r+2) → OnePoint ℕ)
    (ho : OrderedExtendedNodes (fun i => nodeToExtended (x i)))
    (hi : x (Fin.last (r+1))=∞) :
    ∃ c : CanonicalCandidate q r, c.x=x := by
  classical
  have hx : Function.Injective x := by
    intro i j hij
    exact orderedExtendedNodes_injective ho (congrArg nodeToExtended hij)
  obtain ⟨d,hd⟩ := full_interpolation (q : ℝ) hq r (fun i => nodeToExtended (x i))
    (nodeToExtended_injective.comp hx) (fun i => (-1 : ℝ)^(i : ℕ))
  have hd' : ∀ i, polynomialNode (q : ℝ) d.1 (coefficientPolynomial d) (x i) =
      ((-1 : ℚ)^(i : ℕ) : ℚ) := by
    intro i
    simpa only [extendedFunction_nodeToExtended, Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using hd i
  obtain ⟨a,b,hdb⟩ := rational_coefficients_of_values q hq r x hx
    (fun i => (-1 : ℚ)^(i : ℕ)) d hd'
  let R := Polynomial.ofFn (r+1) b
  have hdeg : R.natDegree≤r := Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) b)
  have hR : R.map (Rat.castHom ℝ)=coefficientPolynomial d := by
    rw [hdb]; exact coefficientPolynomial_ratCast r a b
  have ha : a=canonicalParity r := by
    have ht := hd' (Fin.last (r+1))
    rw [hi] at ht
    have htR : (a : ℝ)=(-1 : ℝ)^(r+1) := by simpa [polynomialNode, hdb] using ht
    unfold canonicalParity
    exact_mod_cast htR
  have hcontact : ∀ i, polynomialNode (q : ℝ) (canonicalParity r : ℝ)
      (R.map (Rat.castHom ℝ)) (x i)=(-1 : ℝ)^(i : ℕ) := by
    intro i
    rw [hR]
    have hh : d.1=(canonicalParity r : ℝ) := by simp [hdb, ha]
    simpa only [hh, Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using hd' i
  let A := (rationalEvaluationMatrix q r x).transpose
  let v : Fin (r+2) → ℚ := Fin.cons 1 (fun j : Fin (r+1) => (0 : ℚ)^j.val)
  let ν : Fin (r+2) → ℚ := A.det⁻¹ • A.cramer v
  have hdet : A.det≠0 := by simpa [A] using rationalEvaluationMatrix_det_ne_zero q hq r x hx
  have hv : A.mulVec ν=v := by
    dsimp [ν]
    rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  have hmass : ∑ i, ν i=1 := by
    have ht := congrFun hv 0
    simpa [A,v,Matrix.mulVec,dotProduct,rationalEvaluationMatrix] using ht
  have hmom (j : Fin (r+1)) : ∑ i, ν i*rationalNodeMonomial q j.val (x i)=(0 : ℚ)^j.val := by
    have ht := congrFun hv j.succ
    simpa [A,v,Matrix.mulVec,dotProduct,rationalEvaluationMatrix,rationalNodeMonomial,mul_comm] using ht
  have hrep := fun c => finite_rational_reproduction q r (r+2) x ν hmass hmom c
  have hsign := ordered_reproduction_alternating (q : ℝ) hq r
    (fun i => nodeToExtended (x i)) ho (fun i => nodeToExtended_positive (x i))
    (fun i => (ν i : ℝ)) (by simpa only [extendedFunction_nodeToExtended] using hrep)
  refine ⟨⟨x,ho,hi,R,hdeg,hcontact,ν,hmass,hmom,?_⟩,rfl⟩
  intro i
  exact_mod_cast hsign i

end LocalCertification.Certificates
