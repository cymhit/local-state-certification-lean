import LocalCertification.Protocol.MeasurableExecutionBorn

/-! Sequential information for the actual arbitrary-measurable Born executor.
The shared seed is charged zero information, only active measurements contribute,
and the terminal limit uses a.s. termination separately in the two input worlds.
Expected cost remains extended-valued throughout. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory
open LocalCertification.Quantum LocalCertification.Information.KernelHistory
open scoped ENNReal BigOperators
noncomputable section

namespace LocalCertification.Protocol.MeasurableExecution.BornProtocol

universe u v
variable {Z S Ω : Type u} {I : Type v}
  [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

theorem kernel_eq_of_inactive (P : BornProtocol Z S Ω I) (ρ σ : QIT.State I)
    (m : ℕ) (x : History Z Ω m) (hx : x ∉ active P.toRawRules m) :
    P.kernel ρ m x = P.kernel σ m x := by
  cases hs : state P.toRawRules m x with
  | inl j => rw [P.kernel_apply ρ, P.kernel_apply σ, hs]
  | inr v => exact False.elim (hx ⟨v, hs⟩)

theorem kernel_klDiv_le_of_active (P : BornProtocol Z S Ω I) (ρ σ : QIT.State I)
    (Γ : ℝ)
    (hstep : ∀ s, klDiv ((P.measurements.measurement s).born ρ)
      ((P.measurements.measurement s).born σ) ≤ ENNReal.ofReal Γ)
    (m : ℕ) (x : History Z Ω m) (hx : x ∈ active P.toRawRules m) :
    klDiv (P.kernel ρ m x) (P.kernel σ m x) ≤ ENNReal.ofReal Γ := by
  obtain ⟨⟨record, setting⟩, hs⟩ := hx
  rw [P.kernel_apply ρ, P.kernel_apply σ, hs]
  exact (klDiv_map_le _ _ measurable_inr).trans (hstep setting)

/-- Finite-prefix information is charged to the first input's actual truncated cost. -/
theorem prefix_klDiv_le_expected_min (P : BornProtocol Z S Ω I) (ρ σ : QIT.State I)
    (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hstep : ∀ s, klDiv ((P.measurements.measurement s).born ρ)
      ((P.measurements.measurement s).born σ) ≤ ENNReal.ofReal Γ) (m : ℕ) :
    klDiv (prefixLaw P.seedLaw (P.kernel ρ) m) (prefixLaw P.seedLaw (P.kernel σ) m) ≤
      ENNReal.ofReal Γ * ∫⁻ p, min (P.copyCost p) (m : ℝ≥0∞) ∂P.law ρ := by
  have h := prefixLaw_klDiv_le_activeCount P.seedLaw (P.kernel ρ) (P.kernel σ)
    (active P.toRawRules) (active_measurable P.toRawRules) Γ hΓ
    (P.kernel_eq_of_inactive ρ σ) (P.kernel_klDiv_le_of_active ρ σ Γ hstep) m
  have hsum : ENNReal.ofReal (∑ i ∈ Finset.range m,
      (prefixLaw P.seedLaw (P.kernel ρ) i).real (active P.toRawRules i)) =
      ∑ i ∈ Finset.range m, prefixLaw P.seedLaw (P.kernel ρ) i (active P.toRawRules i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [ENNReal.ofReal_mul hΓ, hsum, P.expected_min] at h
  exact h

/-- The paper's exact testing information factor under genuine Born execution.
No finite expectation or joint history/outcome Radon--Nikodym kernel is assumed. -/
theorem information_of_errors (P : BornProtocol Z S Ω I) (ρ σ : QIT.State I)
    (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hstep : ∀ s, klDiv ((P.measurements.measurement s).born ρ)
      ((P.measurements.measurement s).born σ) ≤ ENNReal.ofReal Γ)
    (hρ : P.Terminates ρ) (hσ : P.Terminates σ) (j : Fin 2)
    (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (heρ : P.law ρ {p | P.reportedDecision p ≠ j} ≤ ENNReal.ofReal δ)
    (heσ : P.law σ {p | P.reportedDecision p = j} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) ≤
      ENNReal.ofReal Γ * P.expectedCopies ρ := by
  exact LocalCertification.Information.KernelTerminal.information_of_errors
    (P.law ρ) (P.law σ) P.time P.reportedDecision P.time_measurable P.reportedDecision_measurable
    (fun m => History Z Ω m)
    (prefixLaw P.seedLaw (P.kernel ρ)) (prefixLaw P.seedLaw (P.kernel σ))
    (prefixDecisionEvent P.toRawRules j) (prefixDecisionEvent_measurable P.toRawRules j) j
    (P.prefixDecisionEvent_measure ρ j) (P.prefixDecisionEvent_measure σ j) hρ hσ
    (ENNReal.ofReal Γ) (P.prefix_klDiv_le_expected_min ρ σ Γ hΓ hstep)
    δ hδ hhalf heρ heσ

private theorem finTwo_ne_zero (j : Fin 2) : j ≠ 0 ↔ j = 1 := by omega
private theorem finTwo_ne_one (j : Fin 2) : j ≠ 1 ↔ j = 0 := by omega

/-- A valid physical protocol supplies both termination facts and both errors;
the expected cost is charged to the high state in this ordering. -/
theorem information_of_valid_high_low (P : BornProtocol Z S Ω I)
    (ψ : QIT.PureVector I) (a b δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (hv : P.Valid ψ a b δ) (ρ σ : QIT.State I)
    (hρ : a ≤ pureTargetFidelity ψ ρ) (hσ : pureTargetFidelity ψ σ ≤ b)
    (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hstep : ∀ s, klDiv ((P.measurements.measurement s).born ρ)
      ((P.measurements.measurement s).born σ) ≤ ENNReal.ofReal Γ) :
    ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) ≤
      ENNReal.ofReal Γ * P.expectedCopies ρ := by
  have hp := hv.1 ρ hρ
  have hq := hv.2 σ hσ
  apply P.information_of_errors ρ σ Γ hΓ hstep hp.1 hq.1 0 δ hδ hhalf
  · simpa only [finTwo_ne_zero] using hp.2
  · exact hq.2

/-- The opposite physical ordering charges the low state, with the same exact
testing factor and no finite-cost assumption. -/
theorem information_of_valid_low_high (P : BornProtocol Z S Ω I)
    (ψ : QIT.PureVector I) (a b δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (hv : P.Valid ψ a b δ) (ρ σ : QIT.State I)
    (hρ : pureTargetFidelity ψ ρ ≤ b) (hσ : a ≤ pureTargetFidelity ψ σ)
    (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hstep : ∀ s, klDiv ((P.measurements.measurement s).born ρ)
      ((P.measurements.measurement s).born σ) ≤ ENNReal.ofReal Γ) :
    ENNReal.ofReal (LocalCertification.Information.testingThreshold δ) ≤
      ENNReal.ofReal Γ * P.expectedCopies ρ := by
  have hp := hv.2 ρ hρ
  have hq := hv.1 σ hσ
  apply P.information_of_errors ρ σ Γ hΓ hstep hp.1 hq.1 1 δ hδ hhalf
  · simpa only [finTwo_ne_one] using hp.2
  · exact hq.2

end LocalCertification.Protocol.MeasurableExecution.BornProtocol
