import LocalCertification.Quantum.CompleteMUBReadout
import LocalCertification.Protocol.FixedScoreAchievabilityInstances
import CertificationGaussian.CompleteMUBFullControl

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Protocol

/-- Supplied complete MUB bases implement every fixed signed score with lambda0=1 and every positive
window gap. No operator-control or score-existence hypothesis remains. -/
theorem fixedScore_completeMUB_canonical (d r : ℕ) (hd : 2≤d) [NeZero d] (B : CompleteMUB d)
    (lam : ℕ → ℝ) (h0 : lam 0=1) :
    FixedScoreCanonicalConclusion B.basis continuous_of_discreteTopology
      (uniformFiniteOutcome (d+1)) r lam := by
  obtain ⟨C₁,C₂,CM,hC₁,hC₂,hCM,hEvent⟩ := radialMUB_full_readout_haar_eventually
    d r hd B lam (0 : ZMod d × ZMod d) localWeylLabel_card
  let Cbad := radialHighGaussianConstant d r lam+
    2*radialHighGaussianConstant d r (fun j => (lam j)^2)+3
  have hbad : 0≤Cbad := by
    have ha := radialHighGaussianConstant_pos d r (by omega) lam
    have hb := radialHighGaussianConstant_pos d r (by omega) (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  apply fixedScore_canonical_from_event hd B.basis continuous_of_discreteTopology
    (uniformFiniteOutcome (d+1)) r lam h0 C₁ C₂ CM Cbad hC₁ hC₂ hCM hbad
  filter_upwards [hEvent] with n hn
  intro ψ₀
  obtain ⟨hm,hp,hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  exact ⟨{U | complexUnitarySphereAction (QuditIndex d n) U ψ₀∈
    radialReadoutFullBad d n r (completeMUBRecords d) (completeMUBFullRecord B) lam localWeylFin 0 CM},hm,hp,hc⟩


/-- A supplied complete MUB implements every strict gamma window on canonical
compact typical targets, with the original raw protocol and O(n^r log(1/delta)) budget.
The score and target sequence precede every window and confidence level. -/
theorem completeMUB_corollary_three_six (d r : ℕ) (hd : 2≤d) [NeZero d] (B : CompleteMUB d) :
    ∃ (lam : ℕ → ℝ) (good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)),
      lam 0=1 ∧ admissible r (radialPolynomial d r lam) ∧
      envelopeRatio ((d:ℝ)+1) (radialPolynomial d r lam)=gamma ((d:ℝ)+1) r ∧
      (∀ n,IsCompact (good n)) ∧
      (∀ᶠ n : ℕ in atTop,canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤
        ENNReal.ofReal (((n:ℝ)^2)⁻¹)) ∧
      ∀ a b : ℝ,a≤1 → 0≤b → b<1 → gamma ((d:ℝ)+1) r<(a-b)/(1-b) →
      ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤1/2 →
        FixedScoreAchievable B.basis continuous_of_discreteTopology (uniformFiniteOutcome (d+1))
          r lam (radialSecondCoefficientSup d r lam) a b δ (spherePureVector ψ) ∧
        ENat.toENNReal (maximumBudget (spherePureVector ψ) a b δ)≤
          ENNReal.ofReal (K*(n:ℝ)^r*Real.log (1/δ)) := by
  obtain ⟨p,lam,hp,hpoly,h0,hr,_hl,_hu,_hc,hgap⟩ := optimal_radial_parameters d r hd
  obtain ⟨η,ε,good,hcompact,_hnonneg,_hη,_hε,hprob,hscore⟩ :=
    fixedScore_completeMUB_canonical d r hd B lam h0
  refine ⟨lam,good,h0,by rwa [hpoly],by rwa [hpoly],hcompact,hprob.mono (fun _ h => h.1),?_⟩
  intro a b ha hb0 hb1 hg
  have hΔ : 0<scoreWindowGap (lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
      (upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)) a b := by
    rw [hpoly]
    exact hgap a b hb1 hg
  let Δ := scoreWindowGap (lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
    (upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)) a b
  let E := radialSecondCoefficientSup d r lam
  let A := complementLambdaCoefficient d r (fun j => (lam j)^2)
  have hE : 0≤E := (radialSecondCoefficientSup_bounds d r (by omega) lam h0).1.le
  have hA : 0≤A := complementLambdaCoefficient_nonneg d r (by omega) _
  refine ⟨1548*(A+E+1)/Δ^2,by positivity,?_⟩
  filter_upwards [hscore a b ha hb0 hb1.le hΔ,eventually_ge_atTop 1] with n hn hn1
  intro ψ hψ δ hδ hhalf
  have hs := hn ψ hψ δ hδ hhalf
  refine ⟨hs,hs.2.2.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpow : (1:ℝ)≤(n:ℝ)^r := one_le_pow₀ hn'
  have hnu := squared_traceScale_le_polynomial d n r (by omega) hn1 lam
  have hv : cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)+E+1≤(A+E+1)*(n:ℝ)^r := by
    dsimp only [A] at *
    nlinarith
  have hlog : 0≤Real.log (1/δ) := Real.log_nonneg (by
    apply (le_div_iff₀ hδ).mpr
    linarith)
  have hmul := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (show (0:ℝ)≤1548 by norm_num)) (sq_nonneg Δ)) hlog
  convert hmul using 1
  dsimp only [Δ,E]
  ring

end LocalCertification.Protocol
