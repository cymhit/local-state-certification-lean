import LocalCertification.Protocol.FixedScoreAchievabilityCanonical

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {H : Type u} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]
  [CompactSpace H] [SecondCountableTopology H] {d : ℕ} [NeZero d]

/-- The joint score and second-moment bounds on one canonical measurable target sequence fixed before every
window and error: all four original operator bounds plus the genuine 1548 V/Delta² raw protocol. -/
def FixedScoreCanonicalConclusion (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ) : Prop :=
    ∃ (η ε : ℕ → ℝ) (good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)),
      (∀ n,IsCompact (good n)) ∧ (∀ n,0≤η n ∧ 0≤ε n) ∧
      Tendsto η atTop (nhds 0) ∧ Tendsto ε atTop (nhds 0) ∧
      (∀ᶠ n : ℕ in atTop,
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
        ∀ ψ∈good n,completeReadoutLoewner d n r (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1,p.2)) lam (radialSecondCoefficientSup d r lam)
          (η n) (ε n) (spherePureVector ψ)) ∧
      ∀ a b : ℝ,a≤1 → 0≤b → b≤1 →
        0<scoreWindowGap (lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
          (upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)) a b →
        ∀ᶠ n : ℕ in atTop,∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤1/2 →
          FixedScoreAchievable setting hs ν r lam (radialSecondCoefficientSup d r lam) a b δ (spherePureVector ψ)

/-- Full local Haar bases implement every fixed signed score with lambda0=1 and every positive
window gap. No operator-control or score-existence hypothesis remains. -/
theorem fixedScore_haar_canonical (d r : ℕ) (hd : 3≤d) [NeZero d]
    (lam : ℕ → ℝ) (h0 : lam 0=1) :
    FixedScoreCanonicalConclusion (id : LocalUnitary d → LocalUnitary d) continuous_id
      (complexUnitaryHaar (Fin d)) r lam := by
  obtain ⟨C₁,C₂,CM,hC₁,hC₂,hCM,hEvent⟩ := radialHaar_full_readout_haar_eventually
    d r hd lam (0 : ZMod d × ZMod d) localWeylLabel_card
  let Cbad := radialHighGaussianConstant d r lam+
    2*radialHighGaussianConstant d r (fun j => (lam j)^2)+3
  have hbad : 0≤Cbad := by
    have ha := radialHighGaussianConstant_pos d r (by omega) lam
    have hb := radialHighGaussianConstant_pos d r (by omega) (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  apply fixedScore_canonical_from_event (by omega : 2≤d) id continuous_id
    (complexUnitaryHaar (Fin d)) r lam h0 C₁ C₂ CM Cbad hC₁ hC₂ hCM hbad
  filter_upwards [hEvent] with n hn
  intro ψ₀
  obtain ⟨hm,hp,hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  exact ⟨{U | complexUnitarySphereAction (QuditIndex d n) U ψ₀∈
    radialReadoutFullBad d n r (haarBasisRecords d) id lam localWeylFin 0 CM},hm,hp,hc⟩

/-- Actual uniform Pauli basis selection gives the same full arbitrary-score statement at d=2. -/
theorem fixedScore_pauli_canonical (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0=1) :
    FixedScoreCanonicalConclusion pauliBasisUnitary continuous_of_discreteTopology
      (uniformFiniteOutcome 3) r lam := by
  obtain ⟨C₁,C₂,CM,hC₁,hC₂,hCM,hEvent⟩ := radialPauli_full_readout_haar_eventually
    r lam (0 : ZMod 2 × ZMod 2) localWeylLabel_card
  let Cbad := radialHighGaussianConstant 2 r lam+
    2*radialHighGaussianConstant 2 r (fun j => (lam j)^2)+3
  have hbad : 0≤Cbad := by
    have ha := radialHighGaussianConstant_pos 2 r (by omega) lam
    have hb := radialHighGaussianConstant_pos 2 r (by omega) (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  apply fixedScore_canonical_from_event (by norm_num : 2≤(2:ℕ)) pauliBasisUnitary
    continuous_of_discreteTopology (uniformFiniteOutcome 3) r lam h0 C₁ C₂ CM Cbad hC₁ hC₂ hCM hbad
  filter_upwards [hEvent] with n hn
  intro ψ₀
  obtain ⟨hm,hp,hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  exact ⟨{U | complexUnitarySphereAction (QuditIndex 2 n) U ψ₀∈
    radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam localWeylFin 0 CM},hm,hp,hc⟩

end LocalCertification.Protocol
