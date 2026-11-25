import LocalCertification.Paper
import LocalCertification.Protocol.MeasurableExecutionFiltration

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LocalCertification.Protocol
open LocalCertification.Protocol.MeasurableExecution
open scoped ENNReal
noncomputable section
namespace ExecutionRegressionExamples

-- Continuous outcomes are accepted without a finite or discrete sigma algebra.
def stopRules : RawRules Unit Unit ℝ where
  rule _ _ := Sum.inl 0
  measurable_rule _ := measurable_const

theorem stop_zero (p : Sample Unit (Slot ℝ)) : stoppingTime stopRules p = 0 := by
  apply le_antisymm _ zero_le
  exact (stoppingTime_le_iff stopRules p 0).mpr (by
    rintro ⟨v, hv⟩
    cases hv)

example (p : Sample Unit (Slot ℝ)) : cost stopRules p = 0 := by
  simp only [cost, stop_zero, ENat.toENNReal_zero]

example : Capped stopRules 0 := by
  intro p _
  simp only [stop_zero, Nat.cast_zero, le_refl]

def runRules : RawRules Unit Unit ℝ where
  rule _ _ := Sum.inr ()
  measurable_rule _ := measurable_const

def runPath : Sample Unit (Slot ℝ) := ((), fun _ => Sum.inr 0)

theorem run_active (n : ℕ) : PathActive runRules runPath n := by
  induction n with
  | zero => exact ⟨(Fin.elim0, ()), rfl⟩
  | succ n ih =>
    obtain ⟨⟨h, s⟩, hh⟩ := ih
    change ∃ v, advance runRules _ (state runRules n (rawPrefix n runPath)) (Sum.inr 0) = Sum.inr v
    rw [hh]
    exact ⟨(Fin.snoc h (s, 0), ()), rfl⟩

theorem run_legal : Legal runRules runPath := by
  intro n
  exact ⟨fun _ => run_active n, fun _ => ⟨0, rfl⟩⟩

theorem run_infinite : stoppingTime runRules runPath = ⊤ :=
  (stoppingTime_eq_top_iff runRules runPath).mpr run_active

example : cost runRules runPath = ⊤ := by
  simp only [cost, run_infinite, ENat.toENNReal_top]

example (m : ℕ) : min (cost runRules runPath) (m : ℝ≥0∞) = m := by
  simp only [cost, run_infinite, ENat.toENNReal_top, min_top_left]

example (N : ℕ) : ¬ Capped runRules N := by
  intro h
  have ht := h runPath run_legal
  rw [run_infinite] at ht
  exact (not_le_of_gt (ENat.natCast_lt_top N)) ht

-- Null seeds still count for the pointwise cap: seed false stops at zero,
-- seed true continues forever, even when the seed law is dirac false.
def nullSeedRules : RawRules Bool Unit ℝ where
  rule _ p := if p.1 then Sum.inr () else Sum.inl 0
  measurable_rule _ := by
    exact (measurable_of_countable (f := fun b : Bool =>
      if b then (Sum.inr () : Fin 2 ⊕ Unit) else Sum.inl 0)).comp measurable_fst

def nullPath : Sample Bool (Slot ℝ) := (true, fun _ => Sum.inr 0)

theorem null_historySeed (n : ℕ) : historySeed n (rawPrefix n nullPath) = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem null_active (n : ℕ) : PathActive nullSeedRules nullPath n := by
  induction n with
  | zero => exact ⟨(Fin.elim0, ()), rfl⟩
  | succ n ih =>
    obtain ⟨⟨h, s⟩, hh⟩ := ih
    change ∃ v, advance nullSeedRules (historySeed n (rawPrefix n nullPath))
      (state nullSeedRules n (rawPrefix n nullPath)) (Sum.inr 0) = Sum.inr v
    rw [hh, null_historySeed]
    exact ⟨(Fin.snoc h (s, 0), ()), rfl⟩

example (N : ℕ) : ¬ Capped nullSeedRules N := by
  intro h
  have hl : Legal nullSeedRules nullPath :=
    fun n => ⟨fun _ => null_active n, fun _ => ⟨0, rfl⟩⟩
  have ht := h nullPath hl
  rw [(stoppingTime_eq_top_iff nullSeedRules nullPath).mpr null_active] at ht
  exact (not_le_of_gt (ENat.natCast_lt_top N)) ht

example : (Measure.dirac false : Measure Bool) {true} = 0 := by simp

end ExecutionRegressionExamples

#eval IO.println "ExecutionRegression_PASS"
