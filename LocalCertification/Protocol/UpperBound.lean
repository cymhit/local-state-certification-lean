import LocalCertification.Protocol.HaarAchievability
import LocalCertification.Protocol.PauliAchievability

set_option autoImplicit false
open MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- The actual qudit upper bound for every d>=2, using Pauli readout at d=2 and local Haar readout
at d>=3. The explicit exceptional set, constants, and size cutoff are independent of delta. -/
theorem qudit_budget_upper (d r : ℕ) (hd : 2≤d) [NeZero d]
    (a b : ℝ) (ha : a≤1) (hb0 : 0≤b) (hb1 : b<1)
    (hg : gamma ((d:ℝ)+1) r<(a-b)/(1-b)) :
    ∃ K Cbad : ℝ,0<K ∧ 0<Cbad ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (Cbad*((n:ℝ)^8)⁻¹) ∧
        ∀ U,U∉bad → ∀ δ : ℝ,0<δ → δ≤1/2 →
          expectedBudget (haarPureVector ψ₀ U) a b δ≤ENat.toENNReal (maximumBudget (haarPureVector ψ₀ U) a b δ) ∧
          ENat.toENNReal (maximumBudget (haarPureVector ψ₀ U) a b δ)≤
            ENNReal.ofReal (K*(n:ℝ)^r*Real.log (1/δ)) := by
  by_cases hd2 : d=2
  · subst d
    obtain ⟨lam,E,CM,Cbad,_hE,_hCM,hCbad,_h0,_hp,_hr,hall⟩ := pauli_achievability r
    obtain ⟨K,hK,hN⟩ := hall a b ha hb0 hb1 hg
    refine ⟨K,Cbad,hK,hCbad,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    obtain ⟨hm,hprob,hvalid⟩ := hn ψ₀
    refine ⟨pauliReadoutBad n r lam CM ψ₀,hm,hprob,?_⟩
    intro U hU δ hδ hhalf
    exact (hvalid U hU δ hδ hhalf).2.2
  · have hd3 : 3≤d := by omega
    obtain ⟨lam,E,CM,Cbad,_hE,_hCM,hCbad,_h0,_hp,_hr,hall⟩ := haar_achievability d r hd3
    obtain ⟨K,hK,hN⟩ := hall a b ha hb0 hb1 hg
    refine ⟨K,Cbad,hK,hCbad,?_⟩
    filter_upwards [hN] with n hn
    intro ψ₀
    obtain ⟨hm,hprob,hvalid⟩ := hn ψ₀
    refine ⟨haarReadoutBad d n r lam CM ψ₀,hm,hprob,?_⟩
    intro U hU δ hδ hhalf
    exact (hvalid U hU δ hδ hhalf).2.2

end LocalCertification.Protocol
