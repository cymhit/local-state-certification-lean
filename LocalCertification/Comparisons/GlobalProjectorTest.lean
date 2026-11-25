import LocalCertification.Comparisons.GlobalProjectorBorn
import LocalCertification.Comparisons.BoundedIIDTail

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace LocalCertification.Comparisons

/-- A fixed sample cap, depending only on the promise gap and confidence. -/
def globalProjectorCopies (a b δ : ℝ) : ℕ := ⌈2 * Real.log (1 / δ) / (a - b) ^ 2⌉₊

def globalProjectorMean {m : ℕ} (x : Fin m → Bool) : ℝ :=
  (∑ i, projectorOutcome (x i)) / (m : ℝ)

/-- The literal empirical midpoint test, with ties assigned to the high class. -/
def globalProjectorTest (a b : ℝ) {m : ℕ} (x : Fin m → Bool) : Bool :=
  if (a + b) / 2 ≤ globalProjectorMean x then true else false

theorem globalProjectorTest_measurable (a b : ℝ) (m : ℕ) :
    Measurable (@globalProjectorTest a b m) := measurable_of_countable _

theorem globalProjectorCopies_pos {a b δ : ℝ} (hab : b < a) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < globalProjectorCopies a b δ := by
  have hl : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ).mpr hδ1)
  have hp : 0 < 2 * Real.log (1 / δ) / (a - b) ^ 2 := by positivity
  have hc := hp.trans_le (Nat.le_ceil (2 * Real.log (1 / δ) / (a - b) ^ 2))
  exact_mod_cast hc

theorem globalProjectorCopies_confidence {a b δ : ℝ}
    (hab : b < a) (hδ : 0 < δ) :
    Real.exp (-2 * (globalProjectorCopies a b δ : ℝ) * ((a - b) / 2) ^ 2) ≤ δ := by
  have hg : 0 < (a - b) ^ 2 := sq_pos_of_pos (sub_pos.mpr hab)
  have hc := (div_le_iff₀ hg).mp (Nat.le_ceil (2 * Real.log (1 / δ) / (a - b) ^ 2))
  change 2 * Real.log (1 / δ) ≤ (globalProjectorCopies a b δ : ℝ) * (a - b) ^ 2 at hc
  calc
    _ ≤ Real.exp (-Real.log (1 / δ)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = δ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]

theorem globalProjectorCopies_rounding {a b δ : ℝ}
    (hab : b < a) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (globalProjectorCopies a b δ : ℝ) < 2 * Real.log (1 / δ) / (a - b) ^ 2 + 1 := by
  have hl : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ).mpr hδ1)
  exact Nat.ceil_lt_add_one (by positivity)

/-- A universal dimension-free constant, including the integer rounding cost. -/
theorem globalProjectorCopies_upper {a b δ : ℝ}
    (hb : 0 < b) (hab : b < a) (ha : a ≤ 1) (hδ : 0 < δ) (hδh : δ < 1 / 2) :
    (globalProjectorCopies a b δ : ℝ) ≤ 4 * Real.log (1 / δ) / (a - b) ^ 2 := by
  have hδ1 : δ < 1 := by linarith
  have hg : 0 < (a - b) ^ 2 := sq_pos_of_pos (sub_pos.mpr hab)
  have hg1 : (a - b) ^ 2 ≤ 1 := by nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < 1 / δ by positivity)
  have hl' : 1 / 2 ≤ Real.log (1 / δ) := by
    simp only [one_div, inv_inv] at hl
    simpa only [one_div] using (show (1 / 2 : ℝ) ≤ Real.log δ⁻¹ by linarith)
  have hone : 1 ≤ 2 * Real.log (1 / δ) / (a - b) ^ 2 := by
    apply (le_div_iff₀ hg).mpr
    nlinarith
  have hc := globalProjectorCopies_rounding hab hδ hδ1
  have he : 4 * Real.log (1 / δ) / (a - b) ^ 2 =
      2 * (2 * Real.log (1 / δ) / (a - b) ^ 2) := by ring
  rw [he]
  linarith

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem globalProjector_error_high (ψ : QIT.PureVector I) (ρ : QIT.State I)
    {a b δ : ℝ} (hab : b < a) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hhigh : a ≤ LocalCertification.Quantum.pureTargetFidelity ψ ρ) :
    globalProjectorRecordLaw ψ ρ (globalProjectorCopies a b δ)
      {x | globalProjectorTest a b x ≠ true} ≤ ENNReal.ofReal δ := by
  let m := globalProjectorCopies a b δ
  have hm : 0 < m := globalProjectorCopies_pos hab hδ hδ1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := iid_bounded_lower_tail (globalProjectorLaw ψ ρ) projectorOutcome
    (measurable_of_countable _) projectorOutcome_mem hm
    (show 0 ≤ (a - b) / 2 by linarith)
  rw [globalProjector_integral] at hs
  have hsub : {x : Fin m → Bool | globalProjectorTest a b x ≠ true} ⊆
      {x | (∑ i, projectorOutcome (x i)) ≤ (m : ℝ) *
        (LocalCertification.Quantum.pureTargetFidelity ψ ρ - (a - b) / 2)} := by
    intro x hx
    have ht : globalProjectorMean x < (a + b) / 2 := by
      by_contra h
      exact hx (by simp [globalProjectorTest, le_of_not_gt h])
    have ht' : (∑ i, projectorOutcome (x i)) < ((a + b) / 2) * (m : ℝ) :=
      (div_lt_iff₀ hm0).mp ht
    change (∑ i, projectorOutcome (x i)) ≤ _
    have hgap : (a + b) / 2 ≤ LocalCertification.Quantum.pureTargetFidelity ψ ρ - (a - b) / 2 := by
      linarith
    nlinarith
  exact ((measure_mono hsub).trans hs).trans
    (ENNReal.ofReal_le_ofReal (globalProjectorCopies_confidence hab hδ))

theorem globalProjector_error_low (ψ : QIT.PureVector I) (ρ : QIT.State I)
    {a b δ : ℝ} (hab : b < a) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlow : LocalCertification.Quantum.pureTargetFidelity ψ ρ ≤ b) :
    globalProjectorRecordLaw ψ ρ (globalProjectorCopies a b δ)
      {x | globalProjectorTest a b x ≠ false} ≤ ENNReal.ofReal δ := by
  let m := globalProjectorCopies a b δ
  have hm : 0 < m := globalProjectorCopies_pos hab hδ hδ1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := iid_bounded_upper_tail (globalProjectorLaw ψ ρ) projectorOutcome
    (measurable_of_countable _) projectorOutcome_mem hm
    (show 0 ≤ (a - b) / 2 by linarith)
  rw [globalProjector_integral] at hs
  have hsub : {x : Fin m → Bool | globalProjectorTest a b x ≠ false} ⊆
      {x | (m : ℝ) * (LocalCertification.Quantum.pureTargetFidelity ψ ρ + (a - b) / 2) ≤
        ∑ i, projectorOutcome (x i)} := by
    intro x hx
    have ht : (a + b) / 2 ≤ globalProjectorMean x := by
      by_contra h
      exact hx (by simp [globalProjectorTest, h])
    have ht' : ((a + b) / 2) * (m : ℝ) ≤ ∑ i, projectorOutcome (x i) :=
      (le_div_iff₀ hm0).mp ht
    change _ ≤ ∑ i, projectorOutcome (x i)
    have hgap : LocalCertification.Quantum.pureTargetFidelity ψ ρ + (a - b) / 2 ≤ (a + b) / 2 := by
      linarith
    nlinarith
  exact ((measure_mono hsub).trans hs).trans
    (ENNReal.ofReal_le_ofReal (globalProjectorCopies_confidence hab hδ))

/-- Global projective-testing comparison for every density matrix.
The cap is chosen before the target, dimension and input state; the local protocol model is unchanged. -/
theorem global_projector_comparison {a b δ : ℝ}
    (hb : 0 < b) (hab : b < a) (ha : a ≤ 1) (hδ : 0 < δ) (hδh : δ < 1 / 2) :
    0 < globalProjectorCopies a b δ ∧
    (globalProjectorCopies a b δ : ℝ) ≤ 4 * Real.log (1 / δ) / (a - b) ^ 2 ∧
    ∀ (ψ : QIT.PureVector I) (ρ : QIT.State I),
      (a ≤ LocalCertification.Quantum.pureTargetFidelity ψ ρ →
        globalProjectorRecordLaw ψ ρ (globalProjectorCopies a b δ)
          {x | globalProjectorTest a b x ≠ true} ≤ ENNReal.ofReal δ) ∧
      (LocalCertification.Quantum.pureTargetFidelity ψ ρ ≤ b →
        globalProjectorRecordLaw ψ ρ (globalProjectorCopies a b δ)
          {x | globalProjectorTest a b x ≠ false} ≤ ENNReal.ofReal δ) := by
  have hδ1 : δ < 1 := by linarith
  exact ⟨globalProjectorCopies_pos hab hδ hδ1,
    globalProjectorCopies_upper hb hab ha hδ hδh,
    fun ψ ρ => ⟨globalProjector_error_high ψ ρ hab hδ hδ1,
      globalProjector_error_low ψ ρ hab hδ hδ1⟩⟩

end LocalCertification.Comparisons
