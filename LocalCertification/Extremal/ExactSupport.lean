import LocalCertification.Extremal.Interpolation
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
open scoped BigOperators Topology
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

private theorem finset_extension {α : Type*} [Infinite α] [DecidableEq α]
    (s : Finset α) (N : ℕ) (hN : s.card ≤ N) : ∃ t : Finset α, s ⊆ t ∧ t.card = N := by
  obtain ⟨u, hu, hcard⟩ := s.finite_toSet.infinite_compl.exists_subset_card_eq (N-s.card)
  have hd : Disjoint s u := Finset.disjoint_left.mpr (fun a hs hu' => hu hu' hs)
  refine ⟨s ∪ u, Finset.subset_union_left, ?_⟩
  rw [Finset.card_union_of_disjoint hd, hcard]
  omega

/-- Arbitrary data at at most r+2 distinct extended nodes are interpolated. -/
theorem partial_interpolation (q : ℝ) (hq : 1 < q) (r n : ℕ) (hn : n ≤ r+2)
    (x : Fin n → Option ℝ) (hx : Function.Injective x) (v : Fin n → ℝ) :
    ∃ c : CoeffSpace r, ∀ i, extendedFunction q c.1 (coefficientPolynomial c) (x i) = v i := by
  classical
  let s : Finset (Option ℝ) := Finset.univ.image x
  have hs : s.card = n := by simp [s, Finset.card_image_of_injective _ hx]
  obtain ⟨t, hst, ht⟩ := finset_extension s (r+2) (by omega)
  let e : t ≃ Fin (r+2) := Finset.equivFinOfCardEq ht
  let z : Fin (r+2) → Option ℝ := fun j => (e.symm j : t).val
  have hz : Function.Injective z := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  let index : Fin n → Fin (r+2) := fun i => e ⟨x i, hst (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  have hi : Function.Injective index := by
    intro i j hij
    apply hx
    exact congrArg Subtype.val (e.injective hij)
  have hzi (i : Fin n) : z (index i) = x i := by simp [z, index]
  obtain ⟨c, hc⟩ := full_interpolation q hq r z hz (Function.extend index v (fun _ => 0))
  refine ⟨c, ?_⟩
  intro i
  have h := hc (index i)
  rw [hzi i, hi.extend_apply] at h
  exact h

/-- Actual OnePoint labels embedded as positive real nodes; none is infinity. -/
def nodeToExtended : OnePoint ℕ → Option ℝ :=
  fun x => x.elim none (fun k => some ((k+1 : ℕ) : ℝ))

theorem nodeToExtended_injective : Function.Injective nodeToExtended := by
  intro x y h
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => rfl
    | coe k => simp [nodeToExtended] at h
  | coe j =>
    induction y using OnePoint.rec with
    | infty => simp [nodeToExtended] at h
    | coe k =>
      have hjk : j = k := by simpa [nodeToExtended] using h
      subst k
      rfl

theorem nodeToExtended_ne_zero (x : OnePoint ℕ) : nodeToExtended x ≠ some 0 := by
  induction x using OnePoint.rec with
  | infty => simp [nodeToExtended]
  | coe k =>
    simp [nodeToExtended]
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

theorem extendedFunction_nodeToExtended (q h : ℝ) (p : ℝ[X]) (x : OnePoint ℕ) :
    extendedFunction q h p (nodeToExtended x) = polynomialNode q h p x := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe k =>
    simp only [nodeToExtended, OnePoint.elim_some, extendedFunction, Option.elim_some, realFunction]
    exact (polynomialNode_real_formula q h p k).symm

/-- No representation on positive/infinity nodes can have fewer than r+2 atoms. -/
theorem dual_support_lower_bound {n : ℕ} (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin n → OnePoint ℕ) (hx : Function.Injective x) (μ : Fin n → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i)) : r+2 ≤ n := by
  by_contra hn
  have hn' : n+1 ≤ r+2 := by omega
  let z : Fin (n+1) → Option ℝ := Fin.cons (some 0) (fun i => nodeToExtended (x i))
  have hz : Function.Injective z := Fin.cons_injective_of_injective
    (by rintro ⟨i, hi⟩; exact nodeToExtended_ne_zero (x i) hi)
    (nodeToExtended_injective.comp hx)
  obtain ⟨c, hc⟩ := partial_interpolation q hq r (n+1) hn' z hz (Fin.cons 1 (fun _ => 0))
  have hzero : extrapolation r c = 1 := by
    have h := hc 0
    simpa [z, extendedFunction, realFunction, extrapolation_formula] using h
  have hnodes (i : Fin n) : polynomialNode q c.1 (coefficientPolynomial c) (x i) = 0 := by
    have h := hc i.succ
    simpa only [z, Fin.cons_succ, extendedFunction_nodeToExtended] using h
  have h := he c
  simp only [hnodes, mul_zero, Finset.sum_const_zero, hzero] at h
  norm_num at h

theorem finite_extremal_dual_exact (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ (c : CoeffSpace r) (x : Fin (r+2) → OnePoint ℕ) (μ : Fin (r+2) → ℝ),
      c ∈ feasible q r ∧ extrapolation r c = extremalValue q r ∧
      Function.Injective x ∧ (∀ i, μ i ≠ 0) ∧
      (∀ b : CoeffSpace r, extrapolation r b =
        ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i)) ∧
      (∑ i, |μ i| = extremalValue q r) ∧
      (∀ i, μ i * polynomialNode q c.1 (coefficientPolynomial c) (x i) = |μ i|) := by
  obtain ⟨c, n, x, μ, hc, hm, hx, hμ, hn, he, hv, hnrm⟩ := finite_extremal_dual q hq r
  have hn' := dual_support_lower_bound q hq r x hx μ he
  have hnEq : n = r+2 := le_antisymm hn hn'
  subst n
  exact ⟨c, x, μ, hc, hm, hx, hμ, he, hv, hnrm⟩

end LocalCertification.Extremal
