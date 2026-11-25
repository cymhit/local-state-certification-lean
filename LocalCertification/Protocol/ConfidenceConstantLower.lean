import LocalCertification.Protocol.BudgetLower
import LocalCertification.Quantum.ConstantHardPair
import LocalCertification.Information.ConfidenceRange

set_option autoImplicit false
open MeasureTheory InformationTheory Filter LocalCertification.Information LocalCertification.Quantum
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]

/-- Any valid adaptive/random-stopping raw protocol pays a constant-log expected cost on the target
itself. The denominator is a genuine promised mixed state, and no finite expectation is assumed. A single fixed confidence cutoff may be any number below one half. -/
theorem constant_expected_lower_confidence (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (a b δ : ℝ) (ha : a≤1) (hb0 : 0<b) (hb1 : b<1)
    (hD : ((d:ℝ)^n)⁻¹≤b/2) (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2)
    (hδ : 0<δ) (hcut : δ≤δstar)
    (P : QuditProtocol Z d n) (hv : Valid P ψ a b δ) :
    ENNReal.ofReal ((confidenceFactor δstar/(4/b+2))*Real.log (1/δ))≤expectedCopies P ψ.state := by
  have hfac := confidenceFactor_pos δstar hs0 hshalf
  have hL : 0<4/b+2 := by positivity
  have hi := valid_information_high_low P ψ a b δ hv hδ (by linarith)
    ψ.state (constantLowState ψ b hb0 hb1) (by rwa [pureTargetFidelity_self])
    (constantLowState_promised ψ b hb0 hb1 hD) (ENNReal.ofReal (4/b+2))
    (constantLowState_klDiv ψ b hb0 hb1)
  have hdv := (ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr hL)) ENNReal.ofReal_ne_top).mpr hi
  rw [← ENNReal.ofReal_div_of_pos hL] at hdv
  apply (ENNReal.ofReal_le_ofReal ?_).trans hdv
  have h := div_le_div_of_nonneg_right (testingThreshold_confidence_lower δstar hs0 hshalf δ hδ hcut) hL.le
  have he : (confidenceFactor δstar/(4/b+2))*Real.log (1/δ) =
      (confidenceFactor δstar*Real.log (1/δ))/(4/b+2) := by
    field_simp
  rw [he]
  exact h

omit [MeasurableSpace Z] in
/-- Every sufficiently large dimension admits the constant-log lower bound on both canonical budgets
for every pure target. This covers the r_d(g)=0 branch without any target exceptional set. -/
theorem constant_budget_lower_confidence (d : ℕ) (hd : 2≤d) [NeZero d]
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1)
    (δstar : ℝ) (hs0 : 0<δstar) (hshalf : δstar<1/2) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n),∀ a : ℝ,a≤1 →
      ∀ δ : ℝ,0<δ → δ≤δstar →
        ENNReal.ofReal (c*Real.log (1/δ))≤expectedBudget ψ a b δ ∧
        ENNReal.ofReal (c*Real.log (1/δ))≤ENat.toENNReal (maximumBudget ψ a b δ) := by
  have hfac := confidenceFactor_pos δstar hs0 hshalf
  have hd' : (1:ℝ)<d := by exact_mod_cast (show 1<d by omega)
  have ht : Tendsto (fun n : ℕ => ((d:ℝ)^n)⁻¹) atTop (nhds 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0:ℝ)≤(d:ℝ)⁻¹ by positivity) (inv_lt_one_of_one_lt₀ hd')
  refine ⟨confidenceFactor δstar/(4/b+2),by positivity,?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<b/2 by positivity))] with n hn
  intro ψ a ha δ hδ hcut
  have he : ENNReal.ofReal ((confidenceFactor δstar/(4/b+2))*Real.log (1/δ))≤expectedBudget ψ a b δ := by
    apply expectedBudget_lower
    intro Q hv
    have h := constant_expected_lower_confidence ψ a b δ ha hb0 hb1 hn.le δstar hs0 hshalf hδ hcut Q.toRaw hv
    apply h.trans (expectedCopies_le_protocolCost Q.toRaw ψ a b ψ.state ?_)
    exact Or.inl (by rwa [pureTargetFidelity_self])
  exact ⟨he,he.trans (expectedBudget_le_maximumBudget ψ a b δ)⟩

end LocalCertification.Protocol
