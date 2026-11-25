import LocalCertification.Extremal.Alternation

set_option autoImplicit false
open scoped BigOperators Topology
open Set
noncomputable section
namespace LocalCertification.Extremal

theorem exists_increasing_permutation {α : Type*} [LinearOrder α] {n : ℕ}
    (x : Fin n → α) (hx : Function.Injective x) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (fun i => x (e i)) := by
  classical
  let s := Finset.univ.image x
  have hc : s.card = n := by simp [s, Finset.card_image_of_injective _ hx]
  have hex (j : Fin n) : ∃ i, x i = s.orderEmbOfFin hc j := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem hc j)
    exact ⟨i, hi⟩
  choose f hf using hex
  have hfi : Function.Injective f := by
    intro i j hij
    apply (s.orderEmbOfFin hc).injective
    rw [← hf i, ← hf j, hij]
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩
  refine ⟨e, ?_⟩
  intro i j hij
  change x (f i) < x (f j)
  rw [hf i, hf j]
  exact (s.orderEmbOfFin hc).strictMono hij

theorem nodeToExtended_positive (x : OnePoint ℕ) :
    (0 : WithTop ℝ) < optionOrder (nodeToExtended x) := by
  induction x using OnePoint.rec with
  | infty => simp [nodeToExtended, optionOrder]
  | coe k =>
    change ((0:ℝ) : WithTop ℝ) < (((k+1:ℕ):ℝ) : WithTop ℝ)
    apply WithTop.coe_lt_coe.mpr
    positivity

theorem norming_alternating_value (μ g : ℝ) (i : ℕ)
    (hμ : μ ≠ 0) (hs : 0 < (-1 : ℝ)^i * μ) (hn : μ*g = |μ|) : g = (-1 : ℝ)^i := by
  have ha : |μ| = (-1 : ℝ)^i * μ := by
    calc
      |μ| = |(-1 : ℝ)^i * μ| := by simp
      _ = (-1 : ℝ)^i * μ := abs_of_pos hs
  apply mul_left_cancel₀ hμ
  rw [hn, ha, mul_comm]

/-- Actual norming dual with sorted nodes, exact support, alternating weights and contact values. -/
theorem finite_extremal_dual_ordered (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ (c : CoeffSpace r) (x : Fin (r+2) → OnePoint ℕ) (μ : Fin (r+2) → ℝ),
      c ∈ feasible q r ∧ extrapolation r c = extremalValue q r ∧
      Function.Injective x ∧ OrderedExtendedNodes (fun i => nodeToExtended (x i)) ∧
      (∀ i, μ i ≠ 0) ∧
      (∀ b : CoeffSpace r, extrapolation r b =
        ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i)) ∧
      (∑ i, |μ i| = extremalValue q r) ∧
      (∀ i : Fin (r+2), 0 < (-1 : ℝ)^(i : ℕ) * μ i) ∧
      (∀ i : Fin (r+2), polynomialNode q c.1 (coefficientPolynomial c) (x i) = (-1 : ℝ)^(i : ℕ)) := by
  classical
  obtain ⟨c, x, μ, hc, hm, hx, hμ, he, hv, hn⟩ := finite_extremal_dual_exact q hq r
  obtain ⟨e, heord⟩ := exists_increasing_permutation (fun i => optionOrder (nodeToExtended (x i)))
    (optionOrder_injective.comp (nodeToExtended_injective.comp hx))
  have hrep (b : CoeffSpace r) : extrapolation r b =
      ∑ i, μ (e i) * polynomialNode q b.1 (coefficientPolynomial b) (x (e i)) := by
    exact (he b).trans (Fintype.sum_equiv e _ _ (fun i => rfl)).symm
  have hs := ordered_reproduction_alternating q hq r (fun i => nodeToExtended (x (e i)))
    heord (fun i => nodeToExtended_positive (x (e i))) (fun i => μ (e i))
    (by simpa only [extendedFunction_nodeToExtended] using hrep)
  refine ⟨c, x ∘ e, μ ∘ e, hc, hm, hx.comp e.injective, heord,
    (fun i => hμ (e i)), hrep, ?_, hs, ?_⟩
  · exact (Fintype.sum_equiv e _ _ (fun i => rfl)).trans hv
  · intro i
    exact norming_alternating_value (μ (e i)) _ (i : ℕ) (hμ (e i)) (hs i) (hn (e i))

end LocalCertification.Extremal
