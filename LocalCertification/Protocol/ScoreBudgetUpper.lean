import LocalCertification.Protocol.MajorityBornProtocol
import LocalCertification.Protocol.Budgets

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LocalCertification.Quantum LocalCertification.Probability
open scoped ENNReal
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {H : Type u} [MeasurableSpace H] {d n : ℕ} [NeZero d]

/-- The constructed test uses exactly its fixed number of copies, for every physical input. -/
theorem majorityBornProtocol_expectedCopies (setting : H → ProductSetting d n) (hs : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (f : H × CertificationGaussian.QuditIndex d n → ℝ) (hf : Measurable f) (t V Δ δ : ℝ)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) :
    expectedCopies (majorityBornProtocol setting hs μ f hf t V Δ δ) ρ =
      (blockCount δ * blockCopies V Δ : ℕ) :=
  fixedBornProtocol_expectedCopies _ _ _ _ _ _ ρ

/-- Explicit one-copy score hypotheses produce an actual feasible canonical cap and bounds on both
formal budgets. The canonical package is obtained from the constructed raw protocol by the proved
full-image normalization, preserving all seed values and outcome paths in the cap obligation. -/
theorem score_budget_upper (setting : H → ProductSetting d n) (hs : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (f : H × CertificationGaussian.QuditIndex d n → ℝ) (hfm : Measurable f)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) {a b t V Δ δ : ℝ}
    (hV : 1≤V) (hΔ : 0<Δ) (hΔ1 : Δ≤1) (hδ : 0<δ) (hδhalf : δ≤1/2)
    (hf : ∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), MemLp f 2 (completeBornRecordLaw ρ setting hs μ))
    (hv : ∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), variance f (completeBornRecordLaw ρ setting hs μ)≤V)
    (hh : ∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), a≤pureTargetFidelity ψ ρ →
      t+Δ/4≤∫ y,f y∂completeBornRecordLaw ρ setting hs μ)
    (hl : ∀ ρ : QIT.State (CertificationGaussian.QuditIndex d n), pureTargetFidelity ψ ρ≤b →
      (∫ y,f y∂completeBornRecordLaw ρ setting hs μ)+Δ/4≤t) :
    capFeasible ψ a b δ (blockCount δ * blockCopies V Δ) ∧
    expectedBudget ψ a b δ ≤ ENat.toENNReal (maximumBudget ψ a b δ) ∧
    ENat.toENNReal (maximumBudget ψ a b δ) ≤
      ENNReal.ofReal (1548*V/Δ^2*Real.log (1/δ)) := by
  have hV0 : 0<V := lt_of_lt_of_le zero_lt_one hV
  have hδ1 : δ<1 := lt_of_le_of_lt hδhalf (by norm_num)
  have hvalid := majorityBornProtocol_valid setting hs μ f hfm ψ hV0 hΔ hδ hδ1 hf hv hh hl
  have hcap := majorityBornProtocol_capped setting hs μ f hfm t V Δ δ
  have hfeas := capFeasible_of_raw _ ψ a b δ hvalid _ hcap
  refine ⟨hfeas,expectedBudget_le_maximumBudget ψ a b δ,?_⟩
  calc
    ENat.toENNReal (maximumBudget ψ a b δ) ≤
        ((blockCount δ * blockCopies V Δ : ℕ) : ℝ≥0∞) :=
      ENat.toENNReal_mono (maximumBudget_le_of_feasible ψ a b δ _ hfeas)
    _ ≤ ENNReal.ofReal (1548*V/Δ^2*Real.log (1/δ)) := by
      simpa only [ENNReal.ofReal_natCast] using
        ENNReal.ofReal_le_ofReal (majorityBornProtocol_budget hV hΔ hΔ1 hδ hδhalf)

end LocalCertification.Protocol
