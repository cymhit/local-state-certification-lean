import CertificationGaussian.CompleteMUBFullControl
import LocalCertification.Protocol.QuantitativeFixedScore
import LocalCertification.Quantum.CompleteMUBReadout

/-!
# Quantitative score bounds on a common target set

For each fixed score the same family of Haar-typical targets controls both
the mean operator and the full second-moment operator. A complete family of
mutually unbiased bases can be supplied in any dimension where one is known.
-/

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter Set CertificationGaussian
  LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol

/-- Uniform sampling from the supplied bases gives the inverse-cube score
errors and the corresponding finite-size protocol on the same target family. -/
theorem fixedScore_completeMUB_quantitative (d r : ℕ) (hd : 2 ≤ d) [NeZero d]
    (B : CompleteMUB d) (lam : ℕ → ℝ) (h0 : lam 0 = 1) :
    QuantitativeFixedScoreConclusion B.basis continuous_of_discreteTopology
      (uniformFiniteOutcome (d + 1)) r lam := by
  obtain ⟨C₁, C₂, CM, hC₁, hC₂, hCM, hEvent⟩ :=
    radialMUB_full_readout_haar_eventually d r hd B lam
      (0 : ZMod d × ZMod d) localWeylLabel_card
  let Cbad := radialHighGaussianConstant d r lam +
    2 * radialHighGaussianConstant d r (fun j => (lam j)^2) + 3
  have hbad : 0 ≤ Cbad := by
    have ha := radialHighGaussianConstant_pos d r (by omega) lam
    have hb := radialHighGaussianConstant_pos d r (by omega) (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  apply fixedScore_quantitative_from_event hd B.basis continuous_of_discreteTopology
    (uniformFiniteOutcome (d + 1)) r lam h0 C₁ C₂ CM Cbad hC₁ hC₂ hCM hbad
  filter_upwards [hEvent] with n hn
  intro ψ₀
  obtain ⟨hm, hp, hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  exact ⟨{U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈
    radialReadoutFullBad d n r (completeMUBRecords d) (completeMUBFullRecord B)
      lam localWeylFin 0 CM}, hm, hp, hc⟩

universe u
variable {H : Type u} [MeasurableSpace H] {d : ℕ} [NeZero d]

/-- The two Loewner inequalities for each of the mean and full second moment
hold for every member of one measurable target set, with an explicit rate. -/
def QuantitativeScoreBounds (setting : H → LocalUnitary d) (ν : Measure H)
    (r : ℕ) (lam : ℕ → ℝ) : Prop :=
  ∃ Cη Cε : ℝ, 0 < Cη ∧ 0 < Cε ∧
  ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
    (∀ n, MeasurableSet (good n)) ∧
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (((n : ℝ)^2)⁻¹) ∧
      ∀ ψ ∈ good n,
        completeReadoutLoewner d n r (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1, p.2)) lam
          (radialSecondCoefficientSup d r lam)
          (Cη * ((n : ℝ)^3)⁻¹) (Cε * ((n : ℝ)^3)⁻¹) (spherePureVector ψ)

private theorem scoreBounds_of_quantitative [TopologicalSpace H] [BorelSpace H]
    [SecondCountableTopology H] (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ)
    (h : QuantitativeFixedScoreConclusion setting hs ν r lam) :
    QuantitativeScoreBounds setting ν r lam := by
  obtain ⟨Cη, Cε, hη, hε, good, hcompact, N, hN, hgood⟩ := h
  refine ⟨Cη, Cε, hη, hε, good, fun n => (hcompact n).isClosed.measurableSet, N, hN, ?_⟩
  intro n hn
  exact ⟨(hgood n hn).1, fun ψ hψ => ((hgood n hn).2 ψ hψ).1⟩

/-- Theorem S8 for independent Haar local bases in dimension at least three. -/
theorem quantitativeScoreBounds_haar (d r : ℕ) (hd : 3 ≤ d) [NeZero d]
    (lam : ℕ → ℝ) (h0 : lam 0 = 1) :
    QuantitativeScoreBounds (id : LocalUnitary d → LocalUnitary d)
      (complexUnitaryHaar (Fin d)) r lam :=
  scoreBounds_of_quantitative _ _ _ _ _ (fixedScore_haar_quantitative d r hd lam h0)

/-- Theorem S8 for the three single-qubit Pauli bases. -/
theorem quantitativeScoreBounds_pauli (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0 = 1) :
    QuantitativeScoreBounds pauliBasisUnitary (uniformFiniteOutcome 3) r lam :=
  scoreBounds_of_quantitative _ _ _ _ _ (fixedScore_pauli_quantitative r lam h0)

/-- Proposition S15 specializes the same bounds to any supplied complete MUB. -/
theorem quantitativeScoreBounds_completeMUB (d r : ℕ) (hd : 2 ≤ d) [NeZero d]
    (B : CompleteMUB d) (lam : ℕ → ℝ) (h0 : lam 0 = 1) :
    QuantitativeScoreBounds B.basis (uniformFiniteOutcome (d + 1)) r lam :=
  scoreBounds_of_quantitative _ _ _ _ _ (fixedScore_completeMUB_quantitative d r hd B lam h0)

end LocalCertification.Protocol

