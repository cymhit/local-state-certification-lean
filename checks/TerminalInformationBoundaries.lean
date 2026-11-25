import LocalCertification.Protocol.ProductDensityTerminalInformation
import Lean
open MeasureTheory ProbabilityTheory InformationTheory Set Filter LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal Topology

-- The two terminal-information derivations have identical interfaces, including universes.
open Lean Elab Command in
run_elab do
  let env ← getEnv
  for (a,b) in [(`LocalCertification.Protocol.terminal_binary_information, `LocalCertification.Protocol.terminal_binary_information_via_product_density),
      (`LocalCertification.Protocol.terminal_information_of_errors, `LocalCertification.Protocol.terminal_information_of_errors_via_product_density),
      (`LocalCertification.Protocol.valid_information_high_low, `LocalCertification.Protocol.valid_information_high_low_via_product_density),
      (`LocalCertification.Protocol.valid_information_low_high, `LocalCertification.Protocol.valid_information_low_high_via_product_density)] do
    let some ca := env.find? a | throwError "Missing comparison declaration"
    let some cb := env.find? b | throwError "Missing binary comparison declaration"
    unless ca.type == cb.type do throwError "Terminal interface mismatch: {a}"
  logInfo "TERMINAL_INTERFACES_IDENTICAL"

example (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) :
    ENNReal.ofReal (testingThreshold δ) ≤ klDiv (binaryMeasure 1) (binaryMeasure 0) := by
  exact testingThreshold_le_binary_klDiv_via_derivatives δ hδ hhalf 1 0 (by simp; linarith) (by simpa using hδ.le)

example (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (q : Icc (0 : ℝ) 1) (hq : (q : ℝ) ≤ δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ klDiv (binaryMeasure 1) (binaryMeasure q) := by
  exact testingThreshold_le_binary_klDiv_via_derivatives δ hδ hhalf 1 q (by simp; linarith) hq

example (q : ℝ) : Tendsto (fun p => binaryRelativeEntropy p q) (𝓝[<] 1)
    (𝓝 (binaryRelativeEntropy 1 q)) :=
  (binaryRelativeEntropy_source_continuous q).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

-- Zero expected cost is retained; no cancellation of a possibly infinite multiplier.
example (P : QuditProtocol Z d n) (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (L : ℝ≥0∞) (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2)
    (hE : expectedCopies P ρ = 0) :
    klDiv (binaryMeasure ⟨(executionLaw P ρ).real {p | executionDecision P p = j},
      measureReal_nonneg, measureReal_le_one⟩)
      (binaryMeasure ⟨(executionLaw P σ).real {p | executionDecision P p = j},
        measureReal_nonneg, measureReal_le_one⟩) = 0 := by
  have h := terminal_klDiv_via_product_density P ρ σ L hL hρ hσ j
  simpa [hE] using h

-- Finite one-copy information and infinite source expectation remain legal inputs.
example (P : QuditProtocol Z d n) (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (L : ℝ≥0∞) (hf : L ≠ ∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2)
    (hE : expectedCopies P ρ = ∞) :
    klDiv (binaryMeasure ⟨(executionLaw P ρ).real {p | executionDecision P p = j},
      measureReal_nonneg, measureReal_le_one⟩)
      (binaryMeasure ⟨(executionLaw P σ).real {p | executionDecision P p = j},
        measureReal_nonneg, measureReal_le_one⟩) ≤ L * ∞ := by
  simpa [hE] using terminal_klDiv_finite_via_product_density P ρ σ L hf hL hρ hσ j
end LocalCertification.Protocol

open Lean Elab Command in
run_elab do
  logInfo "REGRESSION_CHECK\tTerminalInformationBoundaries\tPASS"
