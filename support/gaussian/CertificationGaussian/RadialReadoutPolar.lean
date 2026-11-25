import CertificationGaussian.RadialPolarApproximation

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Control of the actual two readout operators by the same CFC-corrected low columns.
The definition retains the original complete record law, the original c/e coefficients,
and the actual Euclidean isometry and distance conclusions. -/
def radialReadoutPolarControl {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (C₁ C₂ : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) : Prop :=
  let V := unitaryOrbitMatrix (radialLowOrbitFamily d n r W k0) ψ
  let Q := matrixPolarCorrection V
  Qᴴ*Q=1 ∧ ‖rectangularEuclideanCLM (V-Q)‖≤((n:ℝ)^3)⁻¹ ∧
    (∀ x,‖rectangularEuclideanCLM Q x‖=‖x‖) ∧
    ‖rectangularEuclideanCLM (cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.ofLp)-
      radialPolarCompression d n r W k0
        (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤C₁*((n:ℝ)^3)⁻¹ ∧
    ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary d μ record r lam ((d:ℝ)^n) ψ.ofLp)-
      radialPolarCompression d n r W k0
        (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤C₂*((n:ℝ)^3)⁻¹

/-- The actual full-Haar record B and S satisfy the same polar control outside the explicit high/low bad set.
The constants and the threshold in n are chosen before the local family and sphere vector. -/
theorem radialHaarReadoutPolar_control_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ψ∉radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0 →
      radialReadoutPolarControl d n r (haarBasisRecords d) id lam W k0 C₁ C₂ ψ := by
  obtain ⟨C₁,hC₁,h₁⟩ := radialFirst_polar_approx_eventually d r hd lam k0
  obtain ⟨C₂,hC₂,h₂⟩ := radialSecond_polar_approx_eventually d r hd lam k0
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [h₁,h₂,eventually_ge_atTop 2] with n hn₁ hn₂ hn
  intro W h0 hHS ψ hgood
  have hg : ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      (unitaryOrbitGramError (radialLowOrbitFamily d n r W k0) ψ)‖≤((n:ℝ)^3)⁻¹ :=
    le_of_not_gt (fun h => hgood (Or.inr h))
  have hh₁ : ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialFirstHighWeights d r lam k0) ψ‖≤
      (2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹ :=
    le_of_not_gt (fun h => hgood (Or.inl (Or.inl h)))
  have hh₂ : ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialSecondHighWeights d r lam k0) ψ‖≤
      (2+4*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹ :=
    le_of_not_gt (fun h => hgood (Or.inl (Or.inr h)))
  have hp := radialLow_polar_on_good_event d n r hn W k0 ψ hg
  dsimp only [radialReadoutPolarControl]
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_,?_⟩
  · have he := cardinalityHaar_mean_spectrum d W k0 h0 hHS hcard r lam ψ.val
    simp only [Fintype.card_fin] at he
    rw [he]
    exact hn₁ W ψ hg hh₁
  · have he := cardinalityHaar_auxiliary_spectrum d W k0 h0 hHS hcard r lam ψ.val
    simp only [Fintype.card_fin] at he
    rw [he]
    exact hn₂ W ψ hg hh₂

/-- The finite six-outcome Pauli reference records have the identical actual B/S polar control. -/
theorem radialPauliReadoutPolar_control_eventually (r : ℕ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=4) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ψ∉radialHighSphereBad 2 n r lam W k0 ∪ radialLowSphereBad 2 n r W k0 →
      radialReadoutPolarControl 2 n r pauliBasisRecords pauliFullRecord lam W k0 C₁ C₂ ψ := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialHaarReadoutPolar_control_eventually 2 r (by omega) lam k0 (by simpa using hcard)
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE] with n hn
  intro W h0 hHS ψ hgood
  have h := hn W h0 hHS ψ hgood
  have hb := (cardinalityHaar_mean_spectrum 2 W k0 h0 hHS (by simpa using hcard) r lam ψ.val).trans
    (cardinalityPauli_mean_spectrum W k0 h0 hHS hcard r lam ψ.val).symm
  have hs := (cardinalityHaar_auxiliary_spectrum 2 W k0 h0 hHS (by simpa using hcard) r lam ψ.val).trans
    (cardinalityPauli_auxiliary_spectrum W k0 h0 hHS hcard r lam ψ.val).symm
  simp only [Fintype.card_fin] at hb hs
  dsimp only [radialReadoutPolarControl] at h ⊢
  rw [hb,hs] at h
  exact h

/-- Actual canonical-sphere probability and simultaneous B/S polar control on its explicit measurable good set. -/
theorem radialHaarReadoutPolar_canonicalSphere_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      MeasurableSet (radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0) ∧
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        (radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0)≤
          ENNReal.ofReal ((radialHighGaussianConstant d r lam+
            2*radialHighGaussianConstant d r (fun j => (lam j)^2)+2)*((n:ℝ)^8)⁻¹) ∧
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
        ψ∉radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0 →
        radialReadoutPolarControl d n r (haarBasisRecords d) id lam W k0 C₁ C₂ ψ := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialHaarReadoutPolar_control_eventually d r hd lam k0 hcard
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE,radialHighLow_canonicalSphere_joint_tail d r hd lam k0 hcard] with n hc ht
  intro W h0 hW hHS
  exact ⟨(radialHighSphereBad_measurable d n r lam W k0).union
    (radialLowSphereBad_measurable d n r W k0),ht W h0 hW hHS,hc W h0 hHS⟩

/-- Genuine full-Haar sampling of the state gives actual full-Haar reference-record B/S control.
The threshold is uniform in the local family and initial state; each probability is for that fixed family. -/
theorem radialHaarReadoutPolar_haar_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0} ∧
      complexUnitaryHaar (QuditIndex d n) {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0}≤
          ENNReal.ofReal ((radialHighGaussianConstant d r lam+
            2*radialHighGaussianConstant d r (fun j => (lam j)^2)+2)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex d n) U ψ∉
        radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0 →
        radialReadoutPolarControl d n r (haarBasisRecords d) id lam W k0 C₁ C₂
          (complexUnitarySphereAction (QuditIndex d n) U ψ) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialHaarReadoutPolar_control_eventually d r hd lam k0 hcard
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE,radialHighLow_haar_joint_tail d r hd lam k0 hcard] with n hc ht
  intro W h0 hW hHS ψ
  have hm := (radialHighSphereBad_measurable d n r lam W k0).union
    (radialLowSphereBad_measurable d n r W k0)
  exact ⟨(complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm,
    ht W h0 hW hHS ψ,fun U hU => hc W h0 hHS _ hU⟩

/-- The same genuine full-Haar state event controls both actual finite-Pauli reference-record operators. -/
theorem radialPauliReadoutPolar_haar_eventually (r : ℕ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=4) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin 2) (Fin 2) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialHighSphereBad 2 n r lam W k0 ∪ radialLowSphereBad 2 n r W k0} ∧
      complexUnitaryHaar (QuditIndex 2 n) {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialHighSphereBad 2 n r lam W k0 ∪ radialLowSphereBad 2 n r W k0}≤
          ENNReal.ofReal ((radialHighGaussianConstant 2 r lam+
            2*radialHighGaussianConstant 2 r (fun j => (lam j)^2)+2)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex 2 n) U ψ∉
        radialHighSphereBad 2 n r lam W k0 ∪ radialLowSphereBad 2 n r W k0 →
        radialReadoutPolarControl 2 n r pauliBasisRecords pauliFullRecord lam W k0 C₁ C₂
          (complexUnitarySphereAction (QuditIndex 2 n) U ψ) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialPauliReadoutPolar_control_eventually r lam k0 hcard
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE,radialHighLow_haar_joint_tail 2 r (by omega) lam k0 (by simpa using hcard)] with n hc ht
  intro W h0 hW hHS ψ
  have hm := (radialHighSphereBad_measurable 2 n r lam W k0).union
    (radialLowSphereBad_measurable 2 n r W k0)
  exact ⟨(complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm,
    ht W h0 hW hHS ψ,fun U hU => hc W h0 hHS _ hU⟩

end CertificationGaussian
