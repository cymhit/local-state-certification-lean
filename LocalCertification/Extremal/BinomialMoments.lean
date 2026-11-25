import LocalCertification.Extremal.DegreeHierarchy
import Mathlib.RingTheory.Polynomial.Pochhammer

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

def binomialPolynomial (k : ℕ) : ℝ[X] := (k.factorial : ℝ)⁻¹ • descPochhammer ℝ k

theorem binomialPolynomial_degree (k : ℕ) : (binomialPolynomial k).natDegree ≤ k := by
  exact (Polynomial.natDegree_smul_le _ _).trans (le_of_eq (descPochhammer_natDegree ℝ k))

theorem binomialPolynomial_eval_nat (k w : ℕ) :
    (binomialPolynomial k).eval (w : ℝ) = (w.choose k : ℝ) := by
  rw [binomialPolynomial, Polynomial.eval_smul, smul_eq_mul, Nat.cast_choose_eq_descPochhammer_div]
  ring

theorem binomialPolynomial_eval_zero (k : ℕ) :
    (binomialPolynomial k).eval 0 = if k=0 then 1 else 0 := by
  cases k <;> simp [binomialPolynomial, Polynomial.eval_smul ]

def binomialNode (q : ℝ) (k : ℕ) : OnePoint ℕ → ℝ :=
  fun x => x.elim 0 (fun w => q^(-((w+1 : ℕ) : ℝ)) * ((w+1).choose k : ℝ))

theorem binomialNode_eq_polynomialNode (q : ℝ) (k : ℕ) (x : OnePoint ℕ) :
    binomialNode q k x = polynomialNode q 0 (binomialPolynomial k) x := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe w =>
    rw [polynomialNode_real_formula]
    simp only [binomialNode, OnePoint.elim_some, zero_add, binomialPolynomial_eval_nat]

theorem finite_dual_binomial_moments {n : ℕ} (q : ℝ) (r : ℕ)
    (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i))
    (k : ℕ) (hk : k ≤ r) : ∑ i, μ i * binomialNode q k (x i) = if k=0 then 1 else 0 := by
  have h := finite_dual_polynomial q r x μ he (binomialPolynomial k) ((binomialPolynomial_degree k).trans hk)
  simpa only [binomialPolynomial_eval_zero, binomialNode_eq_polynomialNode] using h.symm

theorem ordered_finite_labels (r : ℕ) (x : Fin (r+2) → OnePoint ℕ)
    (hx : Function.Injective x) (ho : OrderedExtendedNodes (fun i => nodeToExtended (x i)))
    (hinf : x (Fin.last (r+1)) = ∞) :
    ∃ j : Fin (r+1) → ℕ, StrictMono j ∧ ∀ i, (j i : OnePoint ℕ) = x i.castSucc := by
  have hf (i : Fin (r+1)) : x i.castSucc ≠ ∞ := by
    intro hi
    exact (Fin.castSucc_lt_last i).ne (hx (hi.trans hinf.symm))
  choose j hj using (fun i => OnePoint.ne_infty_iff_exists.mp (hf i))
  refine ⟨j, ?_, hj⟩
  intro i k hik
  have h := ho (Fin.castSucc_lt_castSucc_iff.mpr hik)
  dsimp only at h
  rw [← hj i, ← hj k] at h
  change ((((j i+1 : ℕ) : ℝ) : WithTop ℝ)) < ((((j k+1 : ℕ) : ℝ) : WithTop ℝ)) at h
  have h' : j i+1 < j k+1 := by exact_mod_cast (WithTop.coe_lt_coe.mp h)
  omega

/-- The paper's explicit positive integer nodes and binomial moments, including the infinity mass. -/
theorem finite_integer_binomial_certificate (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ (j : Fin (r+1) → ℕ) (μ : Fin (r+1) → ℝ) (μInfinity : ℝ),
      StrictMono j ∧ (∀ i, 0 < j i) ∧ (∀ i, μ i ≠ 0) ∧ μInfinity ≠ 0 ∧
      (∑ i, μ i) + μInfinity = 1 ∧ (∑ i, |μ i|) + |μInfinity| = extremalValue q r ∧
      (∀ i : Fin (r+1), 0 < (-1 : ℝ)^(i : ℕ) * μ i) ∧
      0 < (-1 : ℝ)^(r+1) * μInfinity ∧
      (∀ k ≤ r, ∑ i, μ i * q^(-(j i : ℝ)) * ((j i).choose k : ℝ) = if k=0 then 1 else 0) := by
  obtain ⟨c, x, a, hc, hm, hx, ho, hinf, ha, he, hv, hs, _, _, _⟩ := finite_extremal_dual_complete q hq r
  obtain ⟨j, hj, heq⟩ := ordered_finite_labels r x hx ho hinf
  refine ⟨fun i => j i+1, fun i => a i.castSucc, a (Fin.last (r+1)), ?_,
    (fun i => Nat.zero_lt_succ _), (fun i => ha i.castSucc), ha _, ?_, ?_,
    (fun i => hs i.castSucc), hs (Fin.last (r+1)), ?_⟩
  · intro i k hik
    exact Nat.add_lt_add_right (hj hik) 1
  · have h := finite_dual_mass q r x a he
    rwa [Fin.sum_univ_castSucc] at h
  · rwa [Fin.sum_univ_castSucc] at hv
  · intro k hk
    have h := finite_dual_binomial_moments q r x a he k hk
    rw [Fin.sum_univ_castSucc] at h
    simp only [hinf, binomialNode, OnePoint.elim_infty, mul_zero, add_zero] at h
    simpa only [← heq, OnePoint.elim_some, mul_assoc] using h

end LocalCertification.Extremal
