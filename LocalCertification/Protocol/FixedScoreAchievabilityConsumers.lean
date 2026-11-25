import LocalCertification.Protocol.FixedScoreAchievabilityInstances
import LocalCertification.Extremal.DegreeZero

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Protocol.FixedScoreConsumers

/-- Negative coefficients are allowed, with an actual canonical target event and the original test. -/
theorem signed_pauli_canonical :
    FixedScoreCanonicalConclusion pauliBasisUnitary continuous_of_discreteTopology
      (uniformFiniteOutcome 3) 1 (fun j => if j=0 then 1 else -2) :=
  fixedScore_pauli_canonical 1 _ (by simp)

/-- A concrete nonempty positive-gap window at degree zero consumes the full canonical result,
including the actual quarter-error raw protocol and its exact 1548 budget. -/
theorem degree_zero_quarter_error :
    ∃ (lam : ℕ → ℝ) (good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1)),
      lam 0=1 ∧ (∀ n,IsCompact (good n)) ∧ ∀ᶠ n : ℕ in atTop,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 n)) (good n)ᶜ≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
      ∀ ψ∈good n,FixedScoreAchievable pauliBasisUnitary continuous_of_discreteTopology
        (uniformFiniteOutcome 3) 0 lam (radialSecondCoefficientSup 2 0 lam)
        (3/4) (1/4) (1/4) (spherePureVector ψ) := by
  obtain ⟨p,lam,_hp,hpoly,h0,_hr,_hl,_hu,_hc,hgap⟩ := optimal_radial_parameters 2 0 (by norm_num)
  have hg : gamma ((2:ℝ)+1) 0<((3/4:ℝ)-1/4)/(1-1/4) := by
    rw [gamma_zero _ (by norm_num)]
    norm_num
  have hΔ := hgap (3/4) (1/4) (by norm_num) hg
  rw [← hpoly] at hΔ
  obtain ⟨η,ε,good,hcompact,_hpos,_hη,_hε,hgood,hprotocol⟩ := fixedScore_pauli_canonical 0 lam h0
  refine ⟨lam,good,h0,hcompact,?_⟩
  filter_upwards [hgood,hprotocol (3/4) (1/4) (by norm_num) (by norm_num) (by norm_num) hΔ] with n hn hp
  exact ⟨hn.1,fun ψ hψ => hp ψ hψ (1/4) (by norm_num) (by norm_num)⟩

/-- A genuine qutrit Haar instance also permits signed coefficients, without optimality assumptions. -/
theorem signed_qutrit_haar_canonical :
    FixedScoreCanonicalConclusion (id : LocalUnitary 3 → LocalUnitary 3) continuous_id
      (complexUnitaryHaar (Fin 3)) 2 (fun j => if j=0 then 1 else -1/2) :=
  fixedScore_haar_canonical 3 2 (by norm_num) _ (by simp)

end LocalCertification.Protocol.FixedScoreConsumers
