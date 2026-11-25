import LocalCertification.Extremal.ExactSupport

set_option autoImplicit false
open scoped BigOperators Topology
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

/-- Actual extended evaluation vectors are independent up to the dimension bound. -/
theorem extendedDictionary_linearIndependent (q : ℝ) (hq : 1 < q) (r n : ℕ)
    (hn : n ≤ r+2) (x : Fin n → Option ℝ) (hx : Function.Injective x) :
    LinearIndependent ℝ (fun i => extendedDictionary q r (x i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  obtain ⟨c, hc⟩ := partial_interpolation q hq r n hn x hx (Pi.single j 1)
  have h := congrArg (pairing c) ha
  simpa only [map_sum, map_smul, map_zero, smul_eq_mul, pairing_extendedDictionary,
    hc, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] using h

theorem extendedDictionary_nodeToExtended (q : ℝ) (r : ℕ) (x : OnePoint ℕ) :
    extendedDictionary q r (nodeToExtended x) = evaluationDictionary q r x := by
  induction x using OnePoint.rec with
  | infty => simp [nodeToExtended, extendedDictionary, evaluationDictionary_infty]
  | coe k =>
    simp only [nodeToExtended, OnePoint.elim_some, extendedDictionary, Option.elim_some,
      evaluationDictionary_nat]
    congr 1
    funext j
    rw [inverse_pow_eq_real_decay]

theorem evaluationDictionary_linearIndependent (q : ℝ) (hq : 1 < q) (r n : ℕ)
    (hn : n ≤ r+2) (x : Fin n → OnePoint ℕ) (hx : Function.Injective x) :
    LinearIndependent ℝ (fun i => evaluationDictionary q r (x i)) := by
  simpa only [extendedDictionary_nodeToExtended] using
    extendedDictionary_linearIndependent q hq r n hn (fun i => nodeToExtended (x i))
      (nodeToExtended_injective.comp hx)

/-- Every maximizer saturates every atom of any minimal-variation representation. -/
theorem norming_of_maximizer {n : ℕ} (q : ℝ) (r : ℕ)
    (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i))
    (hv : ∑ i, |μ i| = extremalValue q r) (c : CoeffSpace r)
    (hc : c ∈ feasible q r) (hm : extrapolation r c = extremalValue q r) :
    ∀ i, μ i * polynomialNode q c.1 (coefficientPolynomial c) (x i) = |μ i| := by
  have hle (i : Fin n) : μ i * polynomialNode q c.1 (coefficientPolynomial c) (x i) ≤ |μ i| := by
    calc
      _ ≤ |μ i * polynomialNode q c.1 (coefficientPolynomial c) (x i)| := le_abs_self _
      _ = |μ i| * |polynomialNode q c.1 (coefficientPolynomial c) (x i)| := abs_mul _ _
      _ ≤ |μ i| * 1 := mul_le_mul_of_nonneg_left (hc (x i)) (abs_nonneg _)
      _ = |μ i| := mul_one _
  have hs : ∑ i, μ i * polynomialNode q c.1 (coefficientPolynomial c) (x i) = ∑ i, |μ i| :=
    (he c).symm.trans (hm.trans hv.symm)
  exact fun i => (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hs i (Finset.mem_univ i)

/-- The maximizer in the actual infinite-node feasible set is unique. -/
theorem extremizer_unique (q : ℝ) (hq : 1 < q) (r : ℕ) (c d : CoeffSpace r)
    (hc : c ∈ feasible q r) (hd : d ∈ feasible q r)
    (hcm : extrapolation r c = extremalValue q r)
    (hdm : extrapolation r d = extremalValue q r) : c = d := by
  obtain ⟨a, x, μ, _, _, hx, hμ, he, hv, _⟩ := finite_extremal_dual_exact q hq r
  have hcn := norming_of_maximizer q r x μ he hv c hc hcm
  have hdn := norming_of_maximizer q r x μ he hv d hd hdm
  apply extendedEval_injective q hq r (fun i => nodeToExtended (x i))
    (nodeToExtended_injective.comp hx)
  funext i
  simp only [extendedEval_apply, extendedFunction_nodeToExtended]
  exact mul_left_cancel₀ (hμ i) ((hcn i).trans (hdn i).symm)

theorem existsUnique_extremizer (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃! c : CoeffSpace r, c ∈ feasible q r ∧ extrapolation r c = extremalValue q r := by
  obtain ⟨c, hc, hm⟩ := extremalValue_attained q hq r
  exact ⟨c, ⟨hc, hm⟩, fun d hd => extremizer_unique q hq r d c hd.1 hc hd.2 hm⟩

end LocalCertification.Extremal
