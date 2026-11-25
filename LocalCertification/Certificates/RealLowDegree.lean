import LocalCertification.Certificates.SearchConsumers
import LocalCertification.Extremal.DegreeZero

set_option autoImplicit false
open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Certificates

/-- Real-base monotone-tail estimate, with the actual sequence and a finite starting value. -/
theorem real_weighted_tail (q : ℝ) (hq : 0<q) (f : ℕ → ℝ) (M : ℕ)
    (hpos : ∀ w, M≤w → 0≤f w) (hstep : ∀ w, M≤w → f (w+1)≤q*f w)
    (w : ℕ) (hw : M≤w) : 0≤q⁻¹^w*f w ∧ q⁻¹^w*f w≤q⁻¹^M*f M := by
  constructor
  · exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hq.le) _) (hpos w hw)
  · have ha : Antitone (fun k : ℕ => q⁻¹^(M+k)*f (M+k)) := by
      apply antitone_nat_of_succ_le
      intro k
      calc
        _ ≤ q⁻¹^(M+k+1)*(q*f (M+k)) := by
          rw [← Nat.add_assoc]
          exact mul_le_mul_of_nonneg_left (hstep _ (Nat.le_add_right _ _)) (by positivity)
        _ = q⁻¹^(M+k)*f (M+k) := by rw [pow_succ]; field_simp
    have h := ha (Nat.zero_le (w-M))
    simpa only [Nat.add_zero,Nat.add_sub_of_le hw] using h

/-- A finite prefix and a proved real-polynomial tail yield the original infinite feasibility. -/
theorem real_feasible_of_tail (q : ℝ) (hq : 0<q) (r : ℕ) (c : CoeffSpace r)
    (hh : |c.1|=1) (M : ℕ) (hM : 1≤M)
    (hpos : ∀ w : ℕ, M≤w → 0≤ -c.1*(coefficientPolynomial c).eval (w : ℝ))
    (hstep : ∀ w : ℕ, M≤w →
      -c.1*(coefficientPolynomial c).eval ((w+1 : ℕ) : ℝ)≤
        q*(-c.1*(coefficientPolynomial c).eval (w : ℝ)))
    (hprefix : ∀ w ∈ Finset.Icc 1 M,
      |c.1+q⁻¹^w*(coefficientPolynomial c).eval (w : ℝ)|≤1) : c ∈ feasible q r := by
  have hh2 : c.1^2=1 := by nlinarith [sq_abs c.1]
  have he (w : ℕ) : c.1+q⁻¹^w*(coefficientPolynomial c).eval (w : ℝ)=
      c.1*(1-q⁻¹^w*(-c.1*(coefficientPolynomial c).eval (w : ℝ))) := by
    calc
      _ = c.1+c.1^2*(q⁻¹^w*(coefficientPolynomial c).eval (w : ℝ)) := by rw [hh2]; ring
      _ = _ := by ring
  intro x
  induction x using OnePoint.rec with
  | infty => exact hh.le
  | coe k =>
    rw [polynomialNode_nat]
    by_cases hw : k+1≤M
    · exact hprefix _ (Finset.mem_Icc.mpr ⟨by omega,hw⟩)
    · have hb := real_weighted_tail q hq (fun w => -c.1*(coefficientPolynomial c).eval (w : ℝ)) M hpos hstep (k+1) (by omega)
      have hm := hprefix M (Finset.mem_Icc.mpr ⟨hM,le_rfl⟩)
      rw [he,abs_mul,hh,one_mul] at hm ⊢
      have hmb := abs_le.mp hm
      apply abs_le.mpr
      constructor <;> linarith

/-- A concrete real reproducing dual, with matching variation, proves exact original B. -/
theorem real_finite_attainment (q : ℝ) (hq : 1<q) (r n : ℕ)
    (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ) (c : CoeffSpace r)
    (hc : c ∈ feasible q r)
    (he : ∀ b : CoeffSpace r, extrapolation r b=∑ i, μ i*polynomialNode q b.1 (coefficientPolynomial b) (x i))
    (hn : extrapolation r c=∑ i,|μ i|) : extrapolation r c=extremalValue q r := by
  apply le_antisymm (extrapolation_le_extremalValue q hq r hc)
  obtain ⟨b,hb,hmax⟩ := extremalValue_attained q hq r
  rw [← hmax,hn,he]
  apply Finset.sum_le_sum
  intro i _
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hb (x i)))

def degreeOneRealCandidate (q : ℝ) : CoeffSpace 1 := (1, ![2*q^2,-2*q^2])

theorem degreeOneRealCandidate_eval (q w : ℝ) :
    (coefficientPolynomial (degreeOneRealCandidate q)).eval w=2*q^2*(1-w) := by
  simp [coefficientPolynomial_eval,degreeOneRealCandidate,Fin.sum_univ_succ]
  ring

theorem degreeOneRealCandidate_feasible (q : ℝ) (hq : 2≤q) : degreeOneRealCandidate q ∈ feasible q 1 := by
  have hq0 : 0<q := by linarith
  apply real_feasible_of_tail q hq0 1 _ (by norm_num [degreeOneRealCandidate]) 2 (by omega)
  · intro w hw
    rw [degreeOneRealCandidate_eval]
    change 0≤ -1*(2*q^2*(1-(w : ℝ)))
    have hw' : (2 : ℝ)≤w := by exact_mod_cast hw
    nlinarith [mul_nonneg (sq_nonneg q) (show 0≤(w : ℝ)-1 by linarith)]
  · intro w hw
    rw [degreeOneRealCandidate_eval,degreeOneRealCandidate_eval]
    have hw' : (2 : ℝ)≤w := by exact_mod_cast hw
    change -1*(2*q^2*(1-((w+1 : ℕ) : ℝ)))≤q*(-1*(2*q^2*(1-(w : ℝ))))
    push_cast
    have h : 0≤(q-1)*((w : ℝ)-2)+(q-2) := by
      exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith [mul_nonneg (sq_nonneg q) h]
  · intro w hw
    have hw' := Finset.mem_Icc.mp hw
    have hwcases : w=1 ∨ w=2 := by omega
    rcases hwcases with rfl | rfl <;> rw [degreeOneRealCandidate_eval]
    · norm_num [degreeOneRealCandidate]
    · norm_num [degreeOneRealCandidate]
      field_simp
      norm_num


def degreeOneRealNodes : Fin 3 → OnePoint ℕ := ![(0 : ℕ),(1 : ℕ),∞]
def degreeOneRealDual (q : ℝ) : Fin 3 → ℝ := ![2*q,-q^2,(q-1)^2]

theorem degreeOneRealDual_reproduces (q : ℝ) (hq : q≠0) (b : CoeffSpace 1) :
    extrapolation 1 b=∑ i, degreeOneRealDual q i *
      polynomialNode q b.1 (coefficientPolynomial b) (degreeOneRealNodes i) := by
  simp [degreeOneRealDual,degreeOneRealNodes,Fin.sum_univ_succ,
    polynomialNode_nat,polynomialNode_infty,extrapolation_formula,coefficientPolynomial_eval]
  field_simp
  ring

theorem extremalValue_one_real (q : ℝ) (hq : 2≤q) : extremalValue q 1=2*q^2+1 := by
  have hq0 : 0<q := by linarith
  have hc := degreeOneRealCandidate_feasible q hq
  have he := degreeOneRealDual_reproduces q (ne_of_gt hq0)
  have hn : extrapolation 1 (degreeOneRealCandidate q)=∑ i, |degreeOneRealDual q i| := by
    simp [extrapolation_formula,degreeOneRealCandidate,coefficientPolynomial_eval,
      degreeOneRealDual,Fin.sum_univ_succ,abs_of_nonneg hq0.le,abs_of_nonneg (sq_nonneg q),
      abs_of_nonneg (sq_nonneg (q-1)),abs_mul]
    ring
  have h := real_finite_attainment q (by linarith) 1 3 degreeOneRealNodes
    (degreeOneRealDual q) (degreeOneRealCandidate q) hc he hn
  rw [←h]
  simp [extrapolation_formula,degreeOneRealCandidate,coefficientPolynomial_eval,Fin.sum_univ_succ]
  ring

/-- The degree-one critical value for every real base q ≥ 2. -/
theorem gamma_one_real (q : ℝ) (hq : 2≤q) : gamma q 1=1/(q^2+1) := by
  rw [gamma_eq_extremalValue q (by linarith) 1,extremalValue_one_real q hq]
  have hp : 0<q^2+1 := by positivity
  field_simp
  ring


def degreeTwoRealCandidate (q : ℝ) : CoeffSpace 2 :=
  (-1, ![2*q^3+6*q,-3*q^3-5*q,q^3+q])

theorem degreeTwoRealCandidate_eval (q w : ℝ) :
    (coefficientPolynomial (degreeTwoRealCandidate q)).eval w=
      q*(w-2)*((q^2+1)*w-(q^2+3)) := by
  simp [coefficientPolynomial_eval,degreeTwoRealCandidate,Fin.sum_univ_succ]
  ring

theorem degreeTwoRealCandidate_feasible (q : ℝ) (hq : 4≤q) : degreeTwoRealCandidate q ∈ feasible q 2 := by
  have hq0 : 0<q := by linarith
  apply real_feasible_of_tail q hq0 2 _ (by norm_num [degreeTwoRealCandidate]) 3 (by omega)
  · intro w hw
    rw [degreeTwoRealCandidate_eval]
    change 0≤ -(-1)*(q*((w : ℝ)-2)*((q^2+1)*(w : ℝ)-(q^2+3)))
    have hw' : (3 : ℝ)≤w := by exact_mod_cast hw
    have hs : 0≤(q^2+1)*(w : ℝ)-(q^2+3) := by
      nlinarith [mul_nonneg (show 0≤(w : ℝ)-3 by linarith) (show 0≤q^2+1 by positivity)]
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hq0.le (by linarith)) hs)
  · intro w hw
    rw [degreeTwoRealCandidate_eval,degreeTwoRealCandidate_eval]
    change -(-1)*(q*(((w+1 : ℕ) : ℝ)-2)*((q^2+1)*((w+1 : ℕ) : ℝ)-(q^2+3)))≤
      q*(-(-1)*(q*((w : ℝ)-2)*((q^2+1)*(w : ℝ)-(q^2+3))))
    push_cast
    have hw' : (3 : ℝ)≤w := by exact_mod_cast hw
    have hq2 : 16≤q^2 := by nlinarith
    have hc0 : 0≤q^3-3*q^2-1 := by
      nlinarith [mul_nonneg (show 0≤q-4 by linarith) (sq_nonneg q)]
    have hc1 : 0≤3*q^3-5*q^2+q-3 := by
      nlinarith [mul_nonneg (show 0≤3*q-12 by linarith) (sq_nonneg q)]
    have hc2 : 0≤q*(q-1)*(q^2+1) :=
      mul_nonneg (mul_nonneg hq0.le (by linarith)) (by positivity)
    have h0 := mul_nonneg (show 0≤2*q by positivity) hc0
    have h1 := mul_nonneg (mul_nonneg hq0.le hc1) (show 0≤(w : ℝ)-3 by linarith)
    have h2 := mul_nonneg hc2 (sq_nonneg ((w : ℝ)-3))
    nlinarith only [h0,h1,h2]
  · intro w hw
    have hw' := Finset.mem_Icc.mp hw
    have hwcases : w=1 ∨ w=2 ∨ w=3 := by omega
    rcases hwcases with rfl | rfl | rfl <;> rw [degreeTwoRealCandidate_eval]
    all_goals norm_num [degreeTwoRealCandidate]
    all_goals field_simp
    all_goals norm_num
    have he : (-q^2+((q^2+1)*3-(q^2+3)))/q^2=1 := by field_simp; ring
    rw [he]
    norm_num

def degreeTwoRealNodes : Fin 4 → OnePoint ℕ := ![(0 : ℕ),(1 : ℕ),(2 : ℕ),∞]
def degreeTwoRealDual (q : ℝ) : Fin 4 → ℝ := ![3*q,-3*q^2,q^3,-(q-1)^3]

theorem degreeTwoRealDual_reproduces (q : ℝ) (hq : q≠0) (b : CoeffSpace 2) :
    extrapolation 2 b=∑ i, degreeTwoRealDual q i *
      polynomialNode q b.1 (coefficientPolynomial b) (degreeTwoRealNodes i) := by
  simp [degreeTwoRealDual,degreeTwoRealNodes,Fin.sum_univ_succ,
    polynomialNode_nat,polynomialNode_infty,extrapolation_formula,coefficientPolynomial_eval]
  field_simp
  ring

theorem extremalValue_two_real (q : ℝ) (hq : 4≤q) : extremalValue q 2=2*q^3+6*q-1 := by
  have hq0 : 0<q := by linarith
  have hc := degreeTwoRealCandidate_feasible q hq
  have he := degreeTwoRealDual_reproduces q (ne_of_gt hq0)
  have hqm : 0≤q-1 := by linarith
  have hn : extrapolation 2 (degreeTwoRealCandidate q)=∑ i, |degreeTwoRealDual q i| := by
    simp [extrapolation_formula,degreeTwoRealCandidate,coefficientPolynomial_eval,
      degreeTwoRealDual,Fin.sum_univ_succ,abs_of_nonneg hq0.le,
      abs_of_nonneg (pow_nonneg hq0.le 3),abs_of_nonneg (sq_nonneg q),
      abs_of_nonneg (pow_nonneg hqm 3),abs_mul]
    ring
  have h := real_finite_attainment q (by linarith) 2 4 degreeTwoRealNodes
    (degreeTwoRealDual q) (degreeTwoRealCandidate q) hc he hn
  rw [←h]
  simp [extrapolation_formula,degreeTwoRealCandidate,coefficientPolynomial_eval,Fin.sum_univ_succ]
  ring

/-- The degree-two critical value for every real base q ≥ 4. -/
theorem gamma_two_real (q : ℝ) (hq : 4≤q) : gamma q 2=1/(q*(q^2+3)) := by
  rw [gamma_eq_extremalValue q (by linarith) 2,extremalValue_two_real q hq]
  have hq0 : 0<q := by linarith
  have hp : 0<q^2+3 := by positivity
  field_simp
  ring

end LocalCertification.Certificates
