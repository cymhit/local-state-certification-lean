import LocalCertification.Quantum.ReadoutScoreMoments
import LocalCertification.Quantum.SpectralScoreBounds
import LocalCertification.Protocol.ScoreBudgetUpper
import LocalCertification.Protocol.ScoreGap

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory CertificationGaussian LocalCertification.Quantum LocalCertification.Probability
open scoped BigOperators ENNReal Matrix.Norms.L2Operator MatrixOrder
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {H : Type u} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]
  [CompactSpace H] [SecondCountableTopology H] {d n : ℕ} [NeZero d]

/-- The literal raw test applied to the original real cardinality score and full local readout labels. -/
def cardinalityMajorityProtocol (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ)
    (ψ : QIT.PureVector (QuditIndex d n)) (l u a b V δ : ℝ) :
    QuditProtocol (Fin (blockCount δ * blockCopies V (scoreWindowGap l u a b)) → (Fin n → H)) d n :=
  majorityBornProtocol (localProductSetting setting) (localProductSetting_continuous setting hs).measurable
    (Measure.pi (fun _ : Fin n => ν))
    (cardinalityBornScore setting r lam (WithLp.toLp 2 ψ.amp))
    (cardinalityBornScore_continuous setting hs r lam _).measurable
    (scoreWindowThreshold l u a b) V (scoreWindowGap l u a b) δ

/-- Actual operator control supplies every mean and variance premise of the implemented protocol.
The B and M appearing here are the original first and full second moment operators on the same
complete records; no iid replacement law, supplied moment identity, or input purity is assumed. -/
theorem cardinality_achievable_of_spectral_control {J : Type*} [Fintype J] [DecidableEq J]
    (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ)
    (ψ : QIT.PureVector (QuditIndex d n))
    (Q : Matrix (QuditIndex d n) J ℂ) (hQ : Qᴴ*Q=1) (i : J)
    (c eCoeff : J → ℝ) (hc : c i=1)
    (l u eStar nu εB εM τ a b δ : ℝ)
    (hl : l≤0) (hu : 0≤u) (he : 0≤eStar) (hnu : 0≤nu)
    (hcl : ∀ j,j≠i → l≤c j) (hcu : ∀ j,j≠i → c j≤u)
    (hec : ∀ j,eCoeff j≤eStar)
    (hB : ‖cardinalityReadoutMean d (ν.prod (uniformFiniteOutcome d))
      (fun p : H × Fin d => (setting p.1,p.2)) r lam ((d:ℝ)^n) ψ.amp-
      Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ‖≤εB)
    (hM : ‖cardinalityReadoutSecond d (ν.prod (uniformFiniteOutcome d))
      (fun p : H × Fin d => (setting p.1,p.2)) r lam ((d:ℝ)^n) ψ.amp-
      (nu • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)+
        Q*Matrix.diagonal (fun j => (eCoeff j:ℂ))*Qᴴ)‖≤εM)
    (hP : ‖Q*Matrix.single i i (1:ℂ)*Qᴴ-ψ.state.matrix‖≤τ)
    (ha : a≤1) (hb0 : 0≤b) (hb1 : b≤1) (hg : 0<scoreWindowGap l u a b)
    (hεL : εB+|1-l| *τ≤scoreWindowGap l u a b/4)
    (hεU : εB+|1-u| *τ≤scoreWindowGap l u a b/4) (hεM : εM≤1)
    (hδ : 0<δ) (hδhalf : δ≤1/2) :
    Valid (cardinalityMajorityProtocol setting hs ν r lam ψ l u a b (nu+eStar+1) δ) ψ a b δ ∧
    Capped (cardinalityMajorityProtocol setting hs ν r lam ψ l u a b (nu+eStar+1) δ)
      (blockCount δ * blockCopies (nu+eStar+1) (scoreWindowGap l u a b)) ∧
    expectedBudget ψ a b δ ≤ ENat.toENNReal (maximumBudget ψ a b δ) ∧
    ENat.toENNReal (maximumBudget ψ a b δ) ≤
      ENNReal.ofReal (1548*(nu+eStar+1)/(scoreWindowGap l u a b)^2*Real.log (1/δ)) := by
  let ψv : EuclideanSpace ℂ (QuditIndex d n) := WithLp.toLp 2 ψ.amp
  let s := localProductSetting (n:=n) setting
  have hsm : Measurable s := (localProductSetting_continuous setting hs).measurable
  let μ := Measure.pi (fun _ : Fin n => ν)
  let f := cardinalityBornScore setting r lam ψv
  have hfm : Measurable f := (cardinalityBornScore_continuous setting hs r lam ψv).measurable
  have hV : 1≤nu+eStar+1 := by linarith
  have hV0 : 0<nu+eStar+1 := by linarith
  have hδ1 : δ<1 := lt_of_le_of_lt hδhalf (by norm_num)
  have hΔ1 := (scoreWindowGap_bounds hl hu ha hb0 hb1 hg).2.2.2
  have hf (ρ : QIT.State (QuditIndex d n)) : MemLp f 2 (completeBornRecordLaw ρ s hsm μ) :=
    cardinalityBornScore_memLp setting hs ν ρ r lam ψv
  have hv (ρ : QIT.State (QuditIndex d n)) : variance f (completeBornRecordLaw ρ s hsm μ)≤nu+eStar+1 := by
    have h := spectral_score_second_bound ρ Q hQ eCoeff eStar nu εM he hec _ hM
    exact (cardinalityBornScore_variance_le setting hs ν ρ r lam ψv).trans (h.trans (by linarith))
  have hm (ρ : QIT.State (QuditIndex d n)) :
      (a≤pureTargetFidelity ψ ρ → scoreWindowThreshold l u a b+scoreWindowGap l u a b/4≤
        ∫ z,f z∂completeBornRecordLaw ρ s hsm μ) ∧
      (pureTargetFidelity ψ ρ≤b → (∫ z,f z∂completeBornRecordLaw ρ s hsm μ)+scoreWindowGap l u a b/4≤
        scoreWindowThreshold l u a b) := by
    have he' := spectral_score_mean_bounds ψ ρ Q hQ i c hc l u εB τ hl hu hcl hcu _ hB hP
    change (a≤pureTargetFidelity ψ ρ → scoreWindowThreshold l u a b+scoreWindowGap l u a b/4≤
      ∫ z,cardinalityBornScore setting r lam ψv z∂completeBornRecordLaw ρ (localProductSetting setting)
        (localProductSetting_continuous setting hs).measurable (Measure.pi (fun _ : Fin n => ν))) ∧ _
    rw [cardinalityBornScore_mean setting hs ν ρ r lam ψv]
    exact scoreWindowThreshold_margins hl hu ha hb0 hb1 hg hεL hεU he'.1 he'.2
  have hvalid := majorityBornProtocol_valid s hsm μ f hfm ψ hV0 hg hδ hδ1 hf hv
    (fun ρ => (hm ρ).1) (fun ρ => (hm ρ).2)
  have hcap := majorityBornProtocol_capped s hsm μ f hfm (scoreWindowThreshold l u a b)
    (nu+eStar+1) (scoreWindowGap l u a b) δ
  have hb := score_budget_upper s hsm μ f hfm ψ hV hg hΔ1 hδ hδhalf hf hv
    (fun ρ => (hm ρ).1) (fun ρ => (hm ρ).2)
  exact ⟨hvalid,hcap,hb.2⟩

end LocalCertification.Protocol
