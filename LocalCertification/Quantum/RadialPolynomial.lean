import LocalCertification.Extremal.BinomialMoments
import LocalCertification.Protocol.ScoreGap
import CertificationGaussian.RadialBellWeights
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
open Polynomial Set LocalCertification.Extremal LocalCertification.Protocol
open scoped BigOperators
noncomputable section
namespace LocalCertification.Quantum

private def fallingFactorialSequence : Polynomial.Sequence ℝ where
  elems' := descPochhammer ℝ
  degree_eq' j := by
    rw [Polynomial.degree_eq_natDegree (monic_descPochhammer ℝ j).ne_zero,
      descPochhammer_natDegree]

/-- The true falling factorials span every finite degree bound; coefficients are obtained from the
actual polynomial rather than supplied as an extra hypothesis. -/
theorem polynomial_falling_factorial_expansion (r : ℕ) (p : Polynomial ℝ) (hp : p.natDegree≤r) :
    ∃ a : Fin (r+1) → ℝ, ∑ j, a j • descPochhammer ℝ j.val = p := by
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mp
  have hrange : Set.range (fun j : Fin (r+1) => descPochhammer ℝ j.val) =
      fallingFactorialSequence '' Set.Iic r := by
    ext v
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨j.val,by have hj := j.isLt; change j.val≤r; omega,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,by change j≤r at hj; omega⟩,rfl⟩
  rw [hrange, fallingFactorialSequence.span_degreeLE]
  · exact Polynomial.mem_degreeLE.mpr (Polynomial.degree_le_natDegree.trans (by exact_mod_cast hp))
  · intro j _
    change IsUnit (descPochhammer ℝ j).leadingCoeff
    rw [(monic_descPochhammer ℝ j).leadingCoeff]
    exact isUnit_one

/-- The exact polynomial of the original cardinality score coefficients. -/
def radialPolynomial (d r : ℕ) (lam : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j : Fin (r+1), ((d:ℝ)^j.val*lam j.val) • binomialPolynomial j.val

theorem radialPolynomial_eval_nat (d r w : ℕ) (lam : ℕ → ℝ) :
    (radialPolynomial d r lam).eval (w:ℝ) =
      ∑ j : Fin (r+1), (d:ℝ)^j.val*lam j.val*(w.choose j.val:ℝ) := by
  simp only [radialPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_smul,
    smul_eq_mul,binomialPolynomial_eval_nat]

theorem radialPolynomial_eval_zero (d r : ℕ) (lam : ℕ → ℝ) :
    (radialPolynomial d r lam).eval 0=lam 0 := by
  simpa [Fin.sum_univ_succ] using radialPolynomial_eval_nat d r 0 lam

/-- Every actual bounded-degree polynomial has fixed original lambda coefficients, including degree zero. -/
theorem exists_radialPolynomial (d r : ℕ) (hd : 0<d) (p : Polynomial ℝ) (hp : p.natDegree≤r) :
    ∃ lam : ℕ → ℝ, radialPolynomial d r lam=p := by
  obtain ⟨a,ha⟩ := polynomial_falling_factorial_expansion r p hp
  let lam : ℕ → ℝ := fun j => if hj : j<r+1 then a ⟨j,hj⟩*(j.factorial:ℝ)/(d:ℝ)^j else 0
  refine ⟨lam,?_⟩
  rw [← ha]
  unfold radialPolynomial
  apply Finset.sum_congr rfl
  intro j _
  rw [binomialPolynomial,smul_smul]
  have hd0 : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hf0 : (j.val.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j.val
  congr 1
  simp only [lam,dite_eq_left j.isLt]
  field_simp

/-- The original radial first spectrum equals the actual polynomial evaluated at every natural weight. -/
theorem radialFirstCoefficient_eq_polynomial (d r w : ℕ) (lam : ℕ → ℝ) :
    CertificationGaussian.radialFirstCoefficient d r lam w =
      (((d:ℝ)+1)⁻¹)^w*(radialPolynomial d r lam).eval (w:ℝ) := by
  rw [radialPolynomial_eval_nat]
  rfl

theorem radialFirstCoefficient_zero (d r : ℕ) (lam : ℕ → ℝ) :
    CertificationGaussian.radialFirstCoefficient d r lam 0=lam 0 := by
  rw [radialFirstCoefficient_eq_polynomial]
  simp [radialPolynomial_eval_zero]

/-- Positive weights are precisely the original positive-integer envelope samples. -/
theorem radialFirstCoefficient_envelope (d r : ℕ) (hd : 0<d) (lam : ℕ → ℝ)
    (w : ℕ) (hw : 0<w) :
    lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam) ≤ CertificationGaussian.radialFirstCoefficient d r lam w ∧
    CertificationGaussian.radialFirstCoefficient d r lam w ≤ upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hq : 1<(d:ℝ)+1 := by linarith
  have hw' : w-1+1=w := by omega
  have he : weightedValue ((d:ℝ)+1) (radialPolynomial d r lam) (w-1) =
      CertificationGaussian.radialFirstCoefficient d r lam w := by
    rw [radialFirstCoefficient_eq_polynomial]
    simp only [weightedValue,hw']
  exact ⟨he ▸ lowerEnvelope_le _ hq _ (w-1),he ▸ le_upperEnvelope _ hq _ (w-1)⟩

/-- One polynomial and one original coefficient sequence, both fixed by d,r alone, give identity
coefficient one, the original nonidentity envelopes, and every strict achievable gamma window. -/
theorem optimal_radial_parameters (d r : ℕ) (hd : 2≤d) :
    ∃ (p : Polynomial ℝ) (lam : ℕ → ℝ), admissible r p ∧
      radialPolynomial d r lam=p ∧ lam 0=1 ∧ envelopeRatio ((d:ℝ)+1) p=gamma ((d:ℝ)+1) r ∧
      lowerEnvelope ((d:ℝ)+1) p≤0 ∧ 0≤upperEnvelope ((d:ℝ)+1) p ∧
      (∀ w : ℕ, 0<w → lowerEnvelope ((d:ℝ)+1) p≤CertificationGaussian.radialFirstCoefficient d r lam w ∧
        CertificationGaussian.radialFirstCoefficient d r lam w≤upperEnvelope ((d:ℝ)+1) p) ∧
      ∀ a b : ℝ, b<1 → gamma ((d:ℝ)+1) r<(a-b)/(1-b) →
        0<scoreWindowGap (lowerEnvelope ((d:ℝ)+1) p) (upperEnvelope ((d:ℝ)+1) p) a b := by
  have hd0 : 0<d := lt_of_lt_of_le (by norm_num) hd
  have hd' : (0:ℝ)<d := by exact_mod_cast hd0
  have hq : 1<(d:ℝ)+1 := by linarith
  obtain ⟨p,hp,hr,hl,hu,hgap⟩ := optimal_polynomial_score_gaps ((d:ℝ)+1) hq r
  obtain ⟨lam,he⟩ := exists_radialPolynomial d r hd0 p hp.1
  have hl0 : lam 0=1 := by rw [← radialPolynomial_eval_zero d r lam,he]; exact hp.2
  refine ⟨p,lam,hp,he,hl0,hr,hl,hu,?_,hgap⟩
  intro w hw
  simpa only [he] using radialFirstCoefficient_envelope d r hd0 lam w hw

end LocalCertification.Quantum
