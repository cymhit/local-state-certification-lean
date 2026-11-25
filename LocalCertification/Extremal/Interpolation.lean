import LocalCertification.Extremal.ZeroCount
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.SuccPred

set_option autoImplicit false
open scoped BigOperators Topology
open Set Polynomial
noncomputable section
namespace LocalCertification.Extremal

theorem expPolynomial_not_many_distinct_zeros (r : ℕ) (a h : ℝ) (p : ℝ[X])
    (ha : a ≠ 0) (hh : h ≠ 0) (hp : p.natDegree ≤ r)
    (x : Fin (r+2) → ℝ) (hx : Function.Injective x) : ¬∀ i, expPolynomial a h p (x i) = 0 := by
  classical
  intro hz
  let s : Finset ℝ := Finset.univ.image x
  have hcard : s.card = r+2 := by simp [s, Finset.card_image_of_injective _ hx]
  apply expPolynomial_not_many_zeros r a h p ha hh hp (s.orderEmbOfFin hcard)
    (s.orderEmbOfFin hcard).strictMono
  intro i
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem hcard i)
  simpa only [he] using hz j

/-- The real-variable expression includes extrapolation zero independently of OnePoint labels. -/
def realFunction (q h : ℝ) (p : ℝ[X]) (w : ℝ) : ℝ := h + q ^ (-w) * p.eval w

def extendedFunction (q h : ℝ) (p : ℝ[X]) : Option ℝ → ℝ :=
  fun x => x.elim h (realFunction q h p)

theorem realFunction_expPolynomial (q : ℝ) (hq : 0 < q) (h : ℝ) (p : ℝ[X]) (w : ℝ) :
    q^w * realFunction q h p w = expPolynomial (Real.log q) h p w := by
  have he : q^w * q^(-w) = (1 : ℝ) := by rw [← Real.rpow_add hq]; simp
  simp only [realFunction, expPolynomial, mul_add]
  rw [← mul_assoc, he, one_mul, Real.rpow_def_of_pos hq]
  ring

theorem realFunction_zero_iff (q : ℝ) (hq : 0 < q) (h : ℝ) (p : ℝ[X]) (w : ℝ) :
    realFunction q h p w = 0 ↔ expPolynomial (Real.log q) h p w = 0 := by
  rw [← realFunction_expPolynomial q hq]
  exact (mul_eq_zero_iff_left (ne_of_gt (Real.rpow_pos_of_pos hq w))).symm

private theorem extract_finite_nodes {n : ℕ} (x : Fin n → Option ℝ)
    (hx : Function.Injective x) (hfinite : ∀ i, x i ≠ none) :
    ∃ z : Fin n → ℝ, Function.Injective z ∧ ∀ i, x i = some (z i) := by
  let z : Fin n → ℝ := fun i => (x i).getD 0
  have he (i : Fin n) : x i = some (z i) := by
    cases hi : x i with
    | none => exact (hfinite i hi).elim
    | some t => simp [z, hi]
  refine ⟨z, ?_, he⟩
  intro i j hij
  apply hx
  rw [he i, he j, hij]

/-- r+2 distinct finite/infinity evaluations annihilate only the zero function. -/
theorem extendedFunction_zero_data (q : ℝ) (hq : 1 < q) (r : ℕ) (h : ℝ) (p : ℝ[X])
    (hp : p.natDegree ≤ r) (x : Fin (r+2) → Option ℝ) (hx : Function.Injective x)
    (hz : ∀ i, extendedFunction q h p (x i) = 0) : h = 0 ∧ p = 0 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hh : h = 0 := by
    by_contra hh
    have hfinite (i) : x i ≠ none := by
      intro hi
      have hi' := hz i
      apply hh
      simpa [extendedFunction, hi] using hi'
    obtain ⟨z, hzi, he⟩ := extract_finite_nodes x hx hfinite
    apply expPolynomial_not_many_distinct_zeros r (Real.log q) h p
      (ne_of_gt (Real.log_pos hq)) hh hp z hzi
    intro i
    apply (realFunction_zero_iff q hq0 h p (z i)).mp
    have hi := hz i
    simpa [extendedFunction, he i] using hi
  refine ⟨hh, ?_⟩
  have hex : ∃ i₀ : Fin (r+2), ∀ i : Fin (r+1), x (i₀.succAbove i) ≠ none := by
    classical
    by_cases hn : ∃ j, x j = none
    · obtain ⟨j, hj⟩ := hn
      refine ⟨j, ?_⟩
      intro i hi
      exact Fin.succAbove_ne j i (hx (hi.trans hj.symm))
    · exact ⟨0, fun i hi => hn ⟨_, hi⟩⟩
  obtain ⟨i₀, hi₀⟩ := hex
  obtain ⟨z, hzi, he⟩ := extract_finite_nodes (fun i => x (i₀.succAbove i))
    (hx.comp Fin.succAbove_right_injective) hi₀
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hzi ?_ (by simp; omega)
  intro i
  have hi := hz (i₀.succAbove i)
  rw [he i] at hi
  simp only [extendedFunction, Option.elim_some, realFunction, hh, zero_add] at hi
  exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (Real.rpow_pos_of_pos hq0 (-z i)))


def extendedDictionary (q : ℝ) (r : ℕ) : Option ℝ → CoeffSpace r :=
  fun x => x.elim (1, 0) (fun w => (1, fun j => q^(-w) * w^(j : ℕ)))

theorem pairing_extendedDictionary (q : ℝ) (r : ℕ) (c : CoeffSpace r) (x : Option ℝ) :
    pairing c (extendedDictionary q r x) = extendedFunction q c.1 (coefficientPolynomial c) x := by
  cases x with
  | none => simp [extendedDictionary, extendedFunction, pairing]
  | some w =>
    simp [extendedDictionary, extendedFunction, realFunction, pairing, coefficientPolynomial_eval,
      Finset.mul_sum, mul_left_comm]

def extendedEval (q : ℝ) (r : ℕ) (x : Fin (r+2) → Option ℝ) :
    CoeffSpace r →ₗ[ℝ] (Fin (r+2) → ℝ) :=
  LinearMap.pi (fun i => pairing (extendedDictionary q r (x i)))

theorem extendedEval_apply (q : ℝ) (r : ℕ) (x : Fin (r+2) → Option ℝ)
    (c : CoeffSpace r) (i : Fin (r+2)) :
    extendedEval q r x c i = extendedFunction q c.1 (coefficientPolynomial c) (x i) :=
  (pairing_comm _ _).trans (pairing_extendedDictionary q r c (x i))

theorem extendedEval_injective (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+2) → Option ℝ) (hx : Function.Injective x) : Function.Injective (extendedEval q r x) := by
  have hker (c : CoeffSpace r) (hc : extendedEval q r x c = 0) : c = 0 := by
    have hz (i : Fin (r+2)) : extendedFunction q c.1 (coefficientPolynomial c) (x i) = 0 := by
      simpa only [extendedEval_apply, Pi.zero_apply] using congrFun hc i
    obtain ⟨hh, hp⟩ := extendedFunction_zero_data q hq r c.1 (coefficientPolynomial c)
      (coefficientPolynomial_degree c) x hx hz
    apply Prod.ext
    · exact hh
    · change c.2 = 0
      apply Polynomial.injective_ofFn (r+1)
      simpa only [coefficientPolynomial, map_zero] using hp
  intro c d hcd
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hcd, sub_self]

/-- Invertible evaluation on any r+2 distinct real/infinity nodes, including real zero. -/
theorem extendedEval_bijective (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+2) → Option ℝ) (hx : Function.Injective x) : Function.Bijective (extendedEval q r x) := by
  have hinj := extendedEval_injective q hq r x hx
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
  rw [coeffSpace_finrank, Module.finrank_pi, Fintype.card_fin]

theorem full_interpolation (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin (r+2) → Option ℝ) (hx : Function.Injective x) (v : Fin (r+2) → ℝ) :
    ∃ c : CoeffSpace r, ∀ i, extendedFunction q c.1 (coefficientPolynomial c) (x i) = v i := by
  obtain ⟨c, hc⟩ := (extendedEval_bijective q hq r x hx).2 v
  exact ⟨c, fun i => by simpa only [extendedEval_apply] using congrFun hc i⟩

end LocalCertification.Extremal
