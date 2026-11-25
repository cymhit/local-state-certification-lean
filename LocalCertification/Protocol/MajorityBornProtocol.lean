import LocalCertification.Protocol.BlockRecordGrouping

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical Set LocalCertification.Quantum LocalCertification.Probability
open scoped BigOperators ENNReal
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {H : Type u} [MeasurableSpace H] {d n : ℕ} [NeZero d]
attribute [local instance] executionOutcomeInhabited executionSettingInhabited

/-- The actual fixed-block majority protocol. All labels, block lengths, and the score are chosen
before the unknown input is measured; decision 0 accepts the high class. -/
def majorityBornProtocol (setting : H → ProductSetting d n) (hs : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (f : H × CertificationGaussian.QuditIndex d n → ℝ) (hf : Measurable f) (t V Δ δ : ℝ) :
    QuditProtocol (Fin (blockCount δ * blockCopies V Δ) → H) d n :=
  fixedBornProtocol (blockCount δ * blockCopies V Δ) setting hs
    (rawMajorityDecision f t (blockCopies V Δ) (blockCount δ))
    (rawMajorityDecision_measurable f hf t _ _) μ

/-- All original seeds and all outcome paths obey the exact prescribed deterministic cap. -/
theorem majorityBornProtocol_capped (setting : H → ProductSetting d n) (hs : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (f : H × CertificationGaussian.QuditIndex d n → ℝ) (hf : Measurable f) (t V Δ δ : ℝ) :
    Capped (majorityBornProtocol setting hs μ f hf t V Δ δ) (blockCount δ * blockCopies V Δ) :=
  fixedBornProtocol_capped _ _ _ _ _ _

/-- The literal mean-gap and variance conditions on the actual one-copy Born record imply the actual high-class error bound. -/
theorem majorityBornProtocol_error_high (setting : H → ProductSetting d n) (hs : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (f : H × CertificationGaussian.QuditIndex d n → ℝ) (hfm : Measurable f)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) {t V Δ δ : ℝ}
    (hf : MemLp f 2 (completeBornRecordLaw ρ setting hs μ))
    (hV : 0<V) (hΔ : 0<Δ) (hδ : 0<δ) (hδ1 : δ<1)
    (hv : variance f (completeBornRecordLaw ρ setting hs μ)≤V)
    (hmean : t+Δ/4≤∫ y,f y∂completeBornRecordLaw ρ setting hs μ) :
    executionLaw (majorityBornProtocol setting hs μ f hfm t V Δ δ) ρ
      {p | executionDecision (majorityBornProtocol setting hs μ f hfm t V Δ δ) p=1} ≤ ENNReal.ofReal δ := by
  rw [majorityBornProtocol, fixedBornProtocol_error]
  exact rawMajorityDecision_error_high _ f hfm hf hV hΔ hδ hδ1 hv hmean

theorem majorityBornProtocol_error_low (setting : H → ProductSetting d n) (hs : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (f : H × CertificationGaussian.QuditIndex d n → ℝ) (hfm : Measurable f)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) {t V Δ δ : ℝ}
    (hf : MemLp f 2 (completeBornRecordLaw ρ setting hs μ))
    (hV : 0<V) (hΔ : 0<Δ) (hδ : 0<δ) (hδ1 : δ<1)
    (hv : variance f (completeBornRecordLaw ρ setting hs μ)≤V)
    (hmean : (∫ y,f y∂completeBornRecordLaw ρ setting hs μ)+Δ/4≤t) :
    executionLaw (majorityBornProtocol setting hs μ f hfm t V Δ δ) ρ
      {p | executionDecision (majorityBornProtocol setting hs μ f hfm t V Δ δ) p=0} ≤ ENNReal.ofReal δ := by
  rw [majorityBornProtocol, fixedBornProtocol_error]
  exact rawMajorityDecision_error_low _ f hfm hf hV hΔ hδ hδ1 hv hmean

/-- The deterministic copy budget of the majority protocol satisfies an explicit logarithmic bound. -/
theorem majorityBornProtocol_budget {V Δ δ : ℝ} (hV : 1≤V) (hΔ : 0<Δ) (hΔ1 : Δ≤1)
    (hδ : 0<δ) (hδhalf : δ≤1/2) :
    ((blockCount δ * blockCopies V Δ : ℕ):ℝ)≤1548*V/Δ^2*Real.log (1/δ) := by
  rw [Nat.mul_comm]
  exact block_total_budget hV hΔ hΔ1 hδ hδhalf

/-- Operational soundness from explicit one-copy score conditions. This theorem constructs and executes
the raw test; the later quantum B/S estimates must supply these moment and mean-gap hypotheses. -/
theorem majorityBornProtocol_valid (setting : H → ProductSetting d n) (hs : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (f : H × CertificationGaussian.QuditIndex d n → ℝ) (hfm : Measurable f)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) {a b t V Δ δ : ℝ}
    (hV : 0<V) (hΔ : 0<Δ) (hδ : 0<δ) (hδ1 : δ<1)
    (hf : ∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), MemLp f 2 (completeBornRecordLaw ρ setting hs μ))
    (hv : ∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), variance f (completeBornRecordLaw ρ setting hs μ)≤V)
    (hh : ∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), a≤pureTargetFidelity ψ ρ →
      t+Δ/4≤∫ y,f y∂completeBornRecordLaw ρ setting hs μ)
    (hl : ∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), pureTargetFidelity ψ ρ≤b →
      (∫ y,f y∂completeBornRecordLaw ρ setting hs μ)+Δ/4≤t) :
    Valid (majorityBornProtocol setting hs μ f hfm t V Δ δ) ψ a b δ := by
  have ht (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
      Terminates (majorityBornProtocol setting hs μ f hfm t V Δ δ) ρ := by
    apply Filter.Eventually.of_forall
    intro p
    change executionTime (fixedBornProtocol _ _ _ _ _ _) p ≠ ⊤
    rw [fixedBornProtocol_executionTime]
    exact WithTop.natCast_ne_top _
  constructor
  · intro ρ hρ
    exact ⟨ht ρ,majorityBornProtocol_error_high setting hs μ f hfm ρ (hf ρ) hV hΔ hδ hδ1 (hv ρ) (hh ρ hρ)⟩
  · intro ρ hρ
    exact ⟨ht ρ,majorityBornProtocol_error_low setting hs μ f hfm ρ (hf ρ) hV hΔ hδ hδ1 (hv ρ) (hl ρ hρ)⟩

end LocalCertification.Protocol
