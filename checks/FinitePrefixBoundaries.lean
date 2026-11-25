import Lean
import LocalCertification.Information.ProductDensityChainRule
import LocalCertification.Information.SeedCountingReference
import LocalCertification.Protocol.TerminalInformation
set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set LocalCertification.Information
open scoped ENNReal BigOperators LocalCertification.Information
noncomputable section
universe u v
variable {Z : Type u} {O : Type v} [MeasurableSpace Z] [MeasurableSpace O]
  [Fintype O] [MeasurableSingletonClass O]

example (ν : Measure Z) [IsProbabilityMeasure ν]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) (Option O))
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)]
    (L : ℝ≥0∞) (hf : L ≠ ∞) (hL : ∀ t h, klDiv (κ t h) (η t h) ≤ L) :
    klDiv (prefixLaw ν κ 0) (prefixLaw ν η 0) = 0 := by
  simpa using prefixLaw_klDiv_eq_sum_product_density ν κ η L hf hL 0

example (ν : Measure Z) [IsProbabilityMeasure ν] [Nonempty O]
    (κ η : (m : ℕ) → Kernel (SlotHistory Z O m) O)
    [∀ m, IsMarkovKernel (κ m)] [∀ m, IsMarkovKernel (η m)] (m : ℕ) :
    klDiv (prefixLaw ν (fun t => stopContinue ∅ MeasurableSet.empty (κ t)) m)
      (prefixLaw ν (fun t => stopContinue ∅ MeasurableSet.empty (η t)) m) = 0 := by
  apply le_antisymm _ bot_le
  have hb := prefixLaw_stopped_klDiv_le_product_density ν (fun _ => ∅)
    (fun _ => MeasurableSet.empty) κ η 0 ENNReal.zero_ne_top
    (fun _ _ hh => False.elim (Set.notMem_empty _ hh)) m
  simpa using hb

example {H : Type*} [MeasurableSpace H] (s : Set H) (hs : MeasurableSet s)
    (κ : Kernel H O) (h : H) (hh : h ∉ s) :
    stopContinue s hs κ h {none} = 1 := by
  simp [stopContinue_apply, hh]

example {H : Type*} [MeasurableSpace H] (s : Set H) (hs : MeasurableSet s)
    (κ : Kernel H O) (h : H) (hh : h ∉ s) (o : O) :
    stopContinue s hs κ h {some o} = 0 := by
  simp [stopContinue_apply, hh]

open Lean Elab Command in
run_elab do
  logInfo "REGRESSION_CHECK\tFinitePrefixBoundaries\tPASS"
