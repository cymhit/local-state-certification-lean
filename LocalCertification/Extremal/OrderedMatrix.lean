import LocalCertification.Extremal.InfinityMatrix
import Mathlib.Order.Fin.Tuple
import Mathlib.GroupTheory.Perm.Fin

set_option autoImplicit false
open scoped BigOperators Topology
open Set
noncomputable section
namespace LocalCertification.Extremal

/-- Explicit order adapter: none denotes the TOP endpoint, never the Option bottom order. -/
def optionOrder (x : Option ℝ) : WithTop ℝ := x.elim ⊤ (fun a => (a : WithTop ℝ))

def OrderedExtendedNodes {n : ℕ} (x : Fin n → Option ℝ) : Prop :=
  StrictMono (fun i => optionOrder (x i))

theorem optionOrder_injective : Function.Injective optionOrder := by
  intro x y h
  cases x <;> cases y <;> simp_all [optionOrder]

theorem orderedExtendedNodes_injective {n : ℕ} {x : Fin n → Option ℝ}
    (hx : OrderedExtendedNodes x) : Function.Injective x := by
  intro i j hij
  exact hx.injective (congrArg optionOrder hij)

/-- The only possible infinite node in a strictly increasing tuple is its final node. -/
theorem orderedExtendedNodes_cases (r : ℕ) (x : Fin (r+2) → Option ℝ)
    (hx : OrderedExtendedNodes x) :
    (∃ y : Fin (r+2) → ℝ, StrictMono y ∧ x = fun i => some (y i)) ∨
    (∃ y : Fin (r+1) → ℝ, StrictMono y ∧ x = Fin.snoc (fun i => some (y i)) none) := by
  cases hl : x (Fin.last (r+1)) with
  | none =>
    right
    have hf (i : Fin (r+1)) : x i.castSucc ≠ none := by
      intro hi
      have h := hx (Fin.castSucc_lt_last i)
      simp [optionOrder, hi, hl] at h
    let y : Fin (r+1) → ℝ := fun i => (x i.castSucc).getD 0
    have he (i : Fin (r+1)) : x i.castSucc = some (y i) := by
      cases hi : x i.castSucc with
      | none => exact (hf i hi).elim
      | some a => simp [y, hi]
    refine ⟨y, ?_, ?_⟩
    · intro i j hij
      have h := hx (Fin.castSucc_lt_castSucc_iff.mpr hij)
      simpa [he i, he j, optionOrder] using h
    · funext i
      cases i using Fin.lastCases with
      | last => simpa using hl
      | cast i => simpa using he i
  | some a =>
    left
    have hf (i : Fin (r+2)) : x i ≠ none := by
      intro hi
      have h := hx.monotone (Fin.le_last i)
      simp [optionOrder, hi, hl] at h
    let y : Fin (r+2) → ℝ := fun i => (x i).getD 0
    have he (i : Fin (r+2)) : x i = some (y i) := by
      cases hi : x i with
      | none => exact (hf i hi).elim
      | some a => simp [y, hi]
    refine ⟨y, ?_, funext he⟩
    intro i j hij
    have h := hx hij
    simpa [he i, he j, optionOrder] using h

private theorem same_sign_trans {a b c : ℝ} (hab : 0 < a*b) (hac : 0 < a*c) : 0 < b*c := by
  rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact mul_pos hb ((mul_pos_iff_of_pos_left ha).mp hac)
  · rcases mul_pos_iff.mp hac with ⟨ha', _⟩ | ⟨_, hc⟩
    · exact (not_lt_of_gt ha ha').elim
    · exact mul_pos_of_neg_of_neg hb hc

theorem orderedEvaluationMatrix_det_same_sign (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x y : Fin (r+2) → Option ℝ) (hx : OrderedExtendedNodes x) (hy : OrderedExtendedNodes y) :
    0 < (evaluationMatrix q r x).det * (evaluationMatrix q r y).det := by
  let z : Fin (r+2) → ℝ := fun i => (i : ℕ)
  have hz : StrictMono z := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast hij
  have hsign (v : Fin (r+2) → Option ℝ) (hv : OrderedExtendedNodes v) :
      0 < (realEvaluationMatrix q r z).det * (evaluationMatrix q r v).det := by
    rcases orderedExtendedNodes_cases r v hv with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact realEvaluationMatrix_det_same_sign q hq r z a hz ha
    · exact real_infinity_det_same_sign q hq r z a hz ha
  exact same_sign_trans (hsign x hx) (hsign y hy)

theorem ordered_replace_prepend (r : ℕ) (x : Fin (r+2) → Option ℝ)
    (hx : OrderedExtendedNodes x) (hp : ∀ i, (0 : WithTop ℝ) < optionOrder (x i))
    (j : Fin (r+2)) : OrderedExtendedNodes (Fin.cons (some 0) (fun i => x (j.succAbove i))) := by
  let f : Fin (r+2) → Option ℝ := Fin.cons (some 0) (fun i => x (j.succAbove i))
  change OrderedExtendedNodes f
  have he : (fun i => optionOrder (f i)) =
      Fin.cons (0 : WithTop ℝ) (fun i => optionOrder (x (j.succAbove i))) := by
    funext i
    cases i using Fin.cases <;> rfl
  unfold OrderedExtendedNodes
  rw [he]
  exact Fin.strictMono_cons.mpr ⟨fun i => hp _, hx.comp (Fin.strictMono_succAbove j)⟩

end LocalCertification.Extremal
