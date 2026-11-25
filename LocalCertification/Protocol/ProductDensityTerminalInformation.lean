import LocalCertification.Protocol.TerminalInformation
import LocalCertification.Information.BinaryKLMonotonicity
import LocalCertification.Information.ProductDensityChainRule

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal LocalCertification.Information Topology
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- The actual Born finite prefix consumes the explicit paper product-density/log
chain. Finiteness is imposed on the one-copy bound, never on expected stopping time. -/
theorem execution_klDiv_le_truncated_cost_finite_via_product_density (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) (m : ℕ) :
    klDiv (executionPrefixLaw P ρ m) (executionPrefixLaw P σ m) ≤
      L * ∫⁻ p, min (executionCost P p) (m : ℝ≥0∞) ∂executionLaw P ρ := by
  rw [← execution_expected_min]
  exact prefixLaw_stopped_klDiv_le_product_density P.seedLaw (activePrefix P.toRawRules)
    (activePrefix_measurable P.toRawRules)
    (fun t => controlledProductBornKernel d n ρ (prefixSetting P.toRawRules t)
      (prefixSetting_measurable P.toRawRules t))
    (fun t => controlledProductBornKernel d n σ (prefixSetting P.toRawRules t)
      (prefixSetting_measurable P.toRawRules t)) L hfinite
    (fun t h _ => hL (prefixSetting P.toRawRules t h)) m

/-- Full binary KL at the actual terminal event, obtained by DPI at the genuine
truncated events, joint lower semicontinuity, and actual stopping-cost MCT. -/
theorem terminal_klDiv_of_truncated_bounds_via_product_density (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hprefix : ∀ m, klDiv (executionPrefixLaw P ρ m) (executionPrefixLaw P σ m) ≤
      L * ∫⁻ p, min (executionCost P p) (m : ℝ≥0∞) ∂executionLaw P ρ)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) :
    klDiv (binaryMeasure ⟨(executionLaw P ρ).real {p | executionDecision P p = j},
      measureReal_nonneg, measureReal_le_one⟩)
      (binaryMeasure ⟨(executionLaw P σ).real {p | executionDecision P p = j},
        measureReal_nonneg, measureReal_le_one⟩) ≤ L * expectedCopies P ρ := by
  let p : ℕ → Icc (0 : ℝ) 1 := fun m =>
    ⟨(executionPrefixLaw P ρ m).real (prefixDecisionEvent P j m), measureReal_nonneg, measureReal_le_one⟩
  let q : ℕ → Icc (0 : ℝ) 1 := fun m =>
    ⟨(executionPrefixLaw P σ m).real (prefixDecisionEvent P j m), measureReal_nonneg, measureReal_le_one⟩
  have hp : Tendsto p atTop (𝓝 ⟨(executionLaw P ρ).real {p | executionDecision P p = j},
      measureReal_nonneg, measureReal_le_one⟩) :=
    tendsto_subtype_rng.mpr (prefixDecisionEvent_probability_tendsto P ρ hρ j)
  have hq : Tendsto q atTop (𝓝 ⟨(executionLaw P σ).real {p | executionDecision P p = j},
      measureReal_nonneg, measureReal_le_one⟩) :=
    tendsto_subtype_rng.mpr (prefixDecisionEvent_probability_tendsto P σ hσ j)
  refine (binary_klDiv_le_liminf p q _ _ hp hq).trans ?_
  apply liminf_le_of_le (by isBoundedDefault)
  intro b hb
  obtain ⟨m, hm⟩ := hb.exists
  apply hm.trans
  refine (binary_klDiv_event_le (executionPrefixLaw P ρ m) (executionPrefixLaw P σ m)
    (prefixDecisionEvent P j m) (prefixDecisionEvent_measurable P j m)).trans
      ((hprefix m).trans ?_)
  rw [← execution_expected_truncations P ρ]
  exact mul_le_mul' le_rfl (le_iSup (fun m : ℕ =>
    ∫⁻ p, min (executionCost P p) (m : ℝ≥0∞) ∂executionLaw P ρ) m)

/-- The finite one-copy paper route has no old prefix-chain dependency. -/
theorem terminal_klDiv_finite_via_product_density (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) :
    klDiv (binaryMeasure ⟨(executionLaw P ρ).real {p | executionDecision P p = j},
      measureReal_nonneg, measureReal_le_one⟩)
      (binaryMeasure ⟨(executionLaw P σ).real {p | executionDecision P p = j},
        measureReal_nonneg, measureReal_le_one⟩) ≤ L * expectedCopies P ρ :=
  terminal_klDiv_of_truncated_bounds_via_product_density P ρ σ L
    (execution_klDiv_le_truncated_cost_finite_via_product_density P ρ σ L hfinite hL) hρ hσ j

/-- Extended-valued compatibility: only the exceptional infinite one-copy bound
uses the original prefix estimate, retaining its `∞ * 0 = 0` boundary behavior. -/
theorem terminal_klDiv_via_product_density (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) :
    klDiv (binaryMeasure ⟨(executionLaw P ρ).real {p | executionDecision P p = j},
      measureReal_nonneg, measureReal_le_one⟩)
      (binaryMeasure ⟨(executionLaw P σ).real {p | executionDecision P p = j},
        measureReal_nonneg, measureReal_le_one⟩) ≤ L * expectedCopies P ρ := by
  by_cases hfinite : L = ∞
  · exact terminal_klDiv_of_truncated_bounds_via_product_density P ρ σ L
      (execution_klDiv_le_truncated_cost P ρ σ L hL) hρ hσ j
  · exact terminal_klDiv_finite_via_product_density P ρ σ L hfinite hL hρ hσ j

theorem terminal_binary_information_via_product_density (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) (δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (hp : 1 - δ ≤ (executionLaw P ρ).real {p | executionDecision P p = j})
    (hq : (executionLaw P σ).real {p | executionDecision P p = j} ≤ δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ :=
  (testingThreshold_le_binary_klDiv_via_derivatives δ hδ hhalf _ _ hp hq).trans
    (terminal_klDiv_via_product_density P ρ σ L hL hρ hσ j)




/-- The source rejects j with probability at most δ, while the target accepts j with probability at most δ. -/
theorem terminal_information_of_errors_via_product_density (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) (δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (hsource : executionLaw P ρ {p | executionDecision P p ≠ j} ≤ ENNReal.ofReal δ)
    (htarget : executionLaw P σ {p | executionDecision P p = j} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsource
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top htarget
  rw [ENNReal.toReal_ofReal hδ.le] at he ht
  have hc := probReal_compl_eq_one_sub (μ := executionLaw P ρ)
    ((executionDecision_measurable P) (measurableSet_singleton j))
  change (executionLaw P ρ).real ({p | executionDecision P p = j}ᶜ) =
    1 - (executionLaw P ρ).real {p | executionDecision P p = j} at hc
  have hp : 1 - δ ≤ (executionLaw P ρ).real {p | executionDecision P p = j} := by
    change (executionLaw P ρ).real ({p | executionDecision P p = j}ᶜ) ≤ δ at he
    rw [hc] at he
    linarith
  exact terminal_binary_information_via_product_density P ρ σ L hL hρ hσ j δ hδ hhalf hp ht

/-- For high-to-low KL, decision 0 accepts the source; this does not exchange the KL arguments. -/
theorem valid_information_high_low_via_product_density (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hvalid : Valid P ψ a b δ) (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hhigh : a ≤ pureTargetFidelity ψ ρ) (hlow : pureTargetFidelity ψ σ ≤ b)
    (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  obtain ⟨hρ, heρ⟩ := hvalid.1 ρ hhigh
  obtain ⟨hσ, heσ⟩ := hvalid.2 σ hlow
  have he : {p | executionDecision P p ≠ 0} = {p | executionDecision P p = 1} := by
    ext p
    have hj : executionDecision P p = 0 ∨ executionDecision P p = 1 := by omega
    rcases hj with hj | hj <;> simp [hj]
  apply terminal_information_of_errors_via_product_density P ρ σ L hL hρ hσ 0 δ hδ hhalf
  · rw [he]
    exact heρ
  · exact heσ

/-- For low-to-high KL, decision 1 accepts the source, preserving the physical parity-selected direction. -/
theorem valid_information_low_high_via_product_density (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hvalid : Valid P ψ a b δ) (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hlow : pureTargetFidelity ψ ρ ≤ b) (hhigh : a ≤ pureTargetFidelity ψ σ)
    (L : ℝ≥0∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  obtain ⟨hρ, heρ⟩ := hvalid.2 ρ hlow
  obtain ⟨hσ, heσ⟩ := hvalid.1 σ hhigh
  have he : {p | executionDecision P p ≠ 1} = {p | executionDecision P p = 0} := by
    ext p
    have hj : executionDecision P p = 0 ∨ executionDecision P p = 1 := by omega
    rcases hj with hj | hj <;> simp [hj]
  apply terminal_information_of_errors_via_product_density P ρ σ L hL hρ hσ 1 δ hδ hhalf
  · rw [he]
    exact heρ
  · exact heσ


theorem terminal_binary_information_finite_via_product_density (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) (δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (hp : 1 - δ ≤ (executionLaw P ρ).real {p | executionDecision P p = j})
    (hq : (executionLaw P σ).real {p | executionDecision P p = j} ≤ δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ :=
  (testingThreshold_le_binary_klDiv_via_derivatives δ hδ hhalf _ _ hp hq).trans
    (terminal_klDiv_finite_via_product_density P ρ σ L hfinite hL hρ hσ j)




/-- The source rejects j with probability at most δ, while the target accepts j with probability at most δ. -/
theorem terminal_information_of_errors_finite_via_product_density (P : QuditProtocol Z d n)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L)
    (hρ : Terminates P ρ) (hσ : Terminates P σ) (j : Fin 2) (δ : ℝ)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (hsource : executionLaw P ρ {p | executionDecision P p ≠ j} ≤ ENNReal.ofReal δ)
    (htarget : executionLaw P σ {p | executionDecision P p = j} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsource
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top htarget
  rw [ENNReal.toReal_ofReal hδ.le] at he ht
  have hc := probReal_compl_eq_one_sub (μ := executionLaw P ρ)
    ((executionDecision_measurable P) (measurableSet_singleton j))
  change (executionLaw P ρ).real ({p | executionDecision P p = j}ᶜ) =
    1 - (executionLaw P ρ).real {p | executionDecision P p = j} at hc
  have hp : 1 - δ ≤ (executionLaw P ρ).real {p | executionDecision P p = j} := by
    change (executionLaw P ρ).real ({p | executionDecision P p = j}ᶜ) ≤ δ at he
    rw [hc] at he
    linarith
  exact terminal_binary_information_finite_via_product_density P ρ σ L hfinite hL hρ hσ j δ hδ hhalf hp ht

/-- For high-to-low KL, decision 0 accepts the source; this does not exchange the KL arguments. -/
theorem valid_information_high_low_finite_via_product_density (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hvalid : Valid P ψ a b δ) (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hhigh : a ≤ pureTargetFidelity ψ ρ) (hlow : pureTargetFidelity ψ σ ≤ b)
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  obtain ⟨hρ, heρ⟩ := hvalid.1 ρ hhigh
  obtain ⟨hσ, heσ⟩ := hvalid.2 σ hlow
  have he : {p | executionDecision P p ≠ 0} = {p | executionDecision P p = 1} := by
    ext p
    have hj : executionDecision P p = 0 ∨ executionDecision P p = 1 := by omega
    rcases hj with hj | hj <;> simp [hj]
  apply terminal_information_of_errors_finite_via_product_density P ρ σ L hfinite hL hρ hσ 0 δ hδ hhalf
  · rw [he]
    exact heρ
  · exact heσ

/-- For low-to-high KL, decision 1 accepts the source, preserving the physical parity-selected direction. -/
theorem valid_information_low_high_finite_via_product_density (P : QuditProtocol Z d n)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (a b δ : ℝ)
    (hvalid : Valid P ψ a b δ) (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n))
    (hlow : pureTargetFidelity ψ ρ ≤ b) (hhigh : a ≤ pureTargetFidelity ψ σ)
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤ L) :
    ENNReal.ofReal (testingThreshold δ) ≤ L * expectedCopies P ρ := by
  obtain ⟨hρ, heρ⟩ := hvalid.2 ρ hlow
  obtain ⟨hσ, heσ⟩ := hvalid.1 σ hhigh
  have he : {p | executionDecision P p ≠ 1} = {p | executionDecision P p = 0} := by
    ext p
    have hj : executionDecision P p = 0 ∨ executionDecision P p = 1 := by omega
    rcases hj with hj | hj <;> simp [hj]
  apply terminal_information_of_errors_finite_via_product_density P ρ σ L hfinite hL hρ hσ 1 δ hδ hhalf
  · rw [he]
    exact heρ
  · exact heσ


end LocalCertification.Protocol
