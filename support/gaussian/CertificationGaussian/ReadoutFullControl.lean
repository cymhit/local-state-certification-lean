import CertificationGaussian.ReadoutFullSecondTail

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Full actual readout control by the same original low CFC compression.
Besides B/S control, both M-nu I-S and M-nu I-Q diag(e) Q-adjoint are bounded. -/
def radialReadoutFullControl {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (C₁ C₂ CM : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) : Prop :=
  radialReadoutPolarControl d n r μ record lam W k0 C₁ C₂ ψ ∧
  cardinalityReadoutSecondError d n r μ record lam ψ≤CM*((n:ℝ)^3)⁻¹ ∧
  ‖rectangularEuclideanCLM (cardinalityReadoutSecond d μ record r lam ((d:ℝ)^n) ψ.ofLp-
      cardinalityReadoutTraceScale d n r (fun j => (lam j)^2) •
        (1:Matrix (QuditIndex d n) (QuditIndex d n) ℂ))-
    radialPolarCompression d n r W k0
      (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤(C₂+CM)*((n:ℝ)^3)⁻¹

/-- The genuine full second moment uses the same low compression as S; this is an actual CLM triangle estimate. -/
theorem radialReadoutFullControl_of_bounds {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (C₁ C₂ CM : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (hc : radialReadoutPolarControl d n r μ record lam W k0 C₁ C₂ ψ)
    (hm : cardinalityReadoutSecondError d n r μ record lam ψ≤CM*((n:ℝ)^3)⁻¹) :
    radialReadoutFullControl d n r μ record lam W k0 C₁ C₂ CM ψ := by
  refine ⟨hc,hm,?_⟩
  have he (A B : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
      (T : EuclideanSpace ℂ (QuditIndex d n) →L[ℂ] EuclideanSpace ℂ (QuditIndex d n)) :
      rectangularEuclideanCLM A-T=rectangularEuclideanCLM (A-B)+(rectangularEuclideanCLM B-T) := by
    simp only [rectangularEuclideanCLM,map_sub]
    abel
  rw [he _ (cardinalityReadoutAuxiliary d μ record r lam ((d:ℝ)^n) ψ.ofLp)]
  exact (norm_add_le _ _).trans ((add_le_add hm hc.2.2.2.2).trans_eq (by ring))

/-- Under genuine full-unitary Haar sampling, one actual measurable event controls the complete full-Haar readout.
All constants and the threshold precede the local family and initial state. No unknown spectral, moment, or radial hypothesis remains. -/
theorem radialHaar_full_readout_haar_eventually (d r : ℕ) (hd : 3≤d) [NeZero d]
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ CM : ℝ,0<C₁ ∧ 0<C₂ ∧ 0<CM ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialReadoutFullBad d n r (haarBasisRecords d) id lam W k0 CM} ∧
      complexUnitaryHaar (QuditIndex d n) {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialReadoutFullBad d n r (haarBasisRecords d) id lam W k0 CM}≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+3)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex d n) U ψ∉
        radialReadoutFullBad d n r (haarBasisRecords d) id lam W k0 CM →
        radialReadoutFullControl d n r (haarBasisRecords d) id lam W k0 C₁ C₂ CM
          (complexUnitarySphereAction (QuditIndex d n) U ψ) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialHaarReadoutPolar_control_eventually d r (by omega) lam k0 hcard
  obtain ⟨CM,hCM,hT⟩ := radialHaar_full_second_canonicalSphere_tail d r hd lam k0 hcard
  refine ⟨C₁,C₂,CM,hC₁,hC₂,hCM,?_⟩
  filter_upwards [hE,hT] with n he ht
  intro W h0 hW hHS ψ
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hm := radialReadoutFullBad_measurable d n r (haarBasisRecords d) id continuous_id lam W k0 CM
  have hp := ht W h0 hW hHS
  rw [← complexUnitaryHaar_orbit_map (QuditIndex d n) ψ,
    Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm] at hp
  refine ⟨(complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm,hp,?_⟩
  intro U hg
  apply radialReadoutFullControl_of_bounds d n r (haarBasisRecords d) id lam W k0 C₁ C₂ CM _
  · exact he W h0 hHS _ (fun h => hg (Or.inl h))
  · exact le_of_not_gt (fun h => hg (Or.inr h))

/-- Under genuine full-unitary Haar sampling, one actual measurable event controls the complete finite-Pauli readout.
All constants and the threshold precede the local family and initial state. No unknown spectral, moment, or radial hypothesis remains. -/
theorem radialPauli_full_readout_haar_eventually (r : ℕ)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=4) :
    ∃ C₁ C₂ CM : ℝ,0<C₁ ∧ 0<C₂ ∧ 0<CM ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin 2) (Fin 2) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam W k0 CM} ∧
      complexUnitaryHaar (QuditIndex 2 n) {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam W k0 CM}≤
        ENNReal.ofReal ((radialHighGaussianConstant 2 r lam+
          2*radialHighGaussianConstant 2 r (fun j => (lam j)^2)+3)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex 2 n) U ψ∉
        radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam W k0 CM →
        radialReadoutFullControl 2 n r pauliBasisRecords pauliFullRecord lam W k0 C₁ C₂ CM
          (complexUnitarySphereAction (QuditIndex 2 n) U ψ) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialPauliReadoutPolar_control_eventually r lam k0 hcard
  obtain ⟨CM,hCM,hT⟩ := radialPauli_full_second_canonicalSphere_tail r lam k0 hcard
  refine ⟨C₁,C₂,CM,hC₁,hC₂,hCM,?_⟩
  filter_upwards [hE,hT] with n he ht
  intro W h0 hW hHS ψ
  let : Nonempty (QuditIndex 2 n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hm := radialReadoutFullBad_measurable 2 n r pauliBasisRecords pauliFullRecord continuous_of_discreteTopology lam W k0 CM
  have hp := ht W h0 hW hHS
  rw [← complexUnitaryHaar_orbit_map (QuditIndex 2 n) ψ,
    Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm] at hp
  refine ⟨(complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm,hp,?_⟩
  intro U hg
  apply radialReadoutFullControl_of_bounds 2 n r pauliBasisRecords pauliFullRecord lam W k0 C₁ C₂ CM _
  · exact he W h0 hHS _ (fun h => hg (Or.inl h))
  · exact le_of_not_gt (fun h => hg (Or.inr h))

end CertificationGaussian
