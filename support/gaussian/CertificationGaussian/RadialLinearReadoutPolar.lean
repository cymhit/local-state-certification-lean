import CertificationGaussian.RadialLinearPolarApproximation

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- One fixed positive rate for both actual high sphere errors and the actual linear low Gram error. -/
def radialLinearReadoutRate (d : ℕ) (ε : ℝ) : ℝ :=
  min (radialLinearSphereRate d ε) ((Real.log (d:ℝ)-2*radialLinearEntropy d ε)/2)

theorem radialLinearReadoutRate_pos (d : ℕ) (hd : 2≤d) (ε : ℝ) (hε : 0<ε)
    (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2) : 0<radialLinearReadoutRate d ε := by
  exact lt_min (radialLinearSphereRate_pos d hd ε hε hgap) (by linarith)

/-- The high and low events are combined under the same actual canonical sphere measure. -/
theorem radialLinearHighLow_canonicalSphere_joint_tail (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        (radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0)≤
          ENNReal.ofReal (4*Real.exp (-radialLinearReadoutRate d ε*n)) := by
  filter_upwards [radialLinearHigh_canonicalSphere_joint_tail d r hd ε hε hhalf hgap lam k0 hcard,
    radialLinearLow_canonicalSphere_tail d hd ε hε hhalf k0 hcard hgap] with n hh hl
  intro W h0 hW hHS
  have hh' := (hh W h0 hW hHS).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (radialLinear_exp_rate_le n _ (radialLinearReadoutRate d ε) (min_le_left _ _)) (by norm_num : (0:ℝ)≤3)))
  have hl' := (hl W hW hHS).trans (ENNReal.ofReal_le_ofReal
    (radialLinear_exp_rate_le n _ (radialLinearReadoutRate d ε) (min_le_right _ _)))
  change _≤ENNReal.ofReal (3*Real.exp (-radialLinearReadoutRate d ε*n)) at hh'
  change _≤ENNReal.ofReal (Real.exp (-radialLinearReadoutRate d ε*n)) at hl'
  refine (measure_union_le _ _).trans ((add_le_add hh' hl').trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- Genuine full-Haar sampling transports this identical high/low event for every initial unit vector. -/
theorem radialLinearHighLow_haar_joint_tail (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      complexUnitaryHaar (QuditIndex d n) {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0}≤
          ENNReal.ofReal (4*Real.exp (-radialLinearReadoutRate d ε*n)) := by
  filter_upwards [radialLinearHighLow_canonicalSphere_joint_tail d r hd ε hε hhalf hgap lam k0 hcard] with n hn
  intro W h0 hW hHS ψ
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hm := (radialLinearHighSphereBad_measurable d n r ε lam W k0).union
    (radialLinearLowSphereBad_measurable d n ε W k0)
  have h := hn W h0 hW hHS
  rw [← complexUnitaryHaar_orbit_map (QuditIndex d n) ψ,
    Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm] at h
  exact h

/-- Control of the actual two readout operators by the same CFC-corrected low columns.
The definition retains the original complete record law, the original c/e coefficients,
and the actual Euclidean isometry and distance conclusions. -/
def radialLinearReadoutPolarControl {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (ε : ℝ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (C₁ C₂ : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) : Prop :=
  let V := unitaryOrbitMatrix (radialLinearLowOrbitFamily d n ε W k0) ψ
  let Q := matrixPolarCorrection V
  Qᴴ*Q=1 ∧ ‖rectangularEuclideanCLM (V-Q)‖≤((n:ℝ)^3)⁻¹ ∧
    (∀ x,‖rectangularEuclideanCLM Q x‖=‖x‖) ∧
    ‖rectangularEuclideanCLM (cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.ofLp)-
      radialLinearPolarCompression d n ε W k0
        (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤C₁*((n:ℝ)^3)⁻¹ ∧
    ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary d μ record r lam ((d:ℝ)^n) ψ.ofLp)-
      radialLinearPolarCompression d n ε W k0
        (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤C₂*((n:ℝ)^3)⁻¹

/-- The actual full-Haar record B and S satisfy the same polar control outside the explicit high/low bad set.
The constants and the threshold in n are chosen before the local family and sphere vector. -/
theorem radialLinearHaarReadoutPolar_control_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ψ∉radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0 →
      radialLinearReadoutPolarControl d n r ε (haarBasisRecords d) id lam W k0 C₁ C₂ ψ := by
  obtain ⟨C₁,hC₁,h₁⟩ := radialLinearFirst_polar_approx_eventually d r hd ε hε hhalf hgap lam k0 hcard
  obtain ⟨C₂,hC₂,h₂⟩ := radialLinearSecond_polar_approx_eventually d r hd ε hε hhalf hgap lam k0 hcard
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [h₁,h₂,eventually_ge_atTop 2] with n hn₁ hn₂ hn
  intro W h0 hHS ψ hgood
  have hg : ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      (unitaryOrbitGramError (radialLinearLowOrbitFamily d n ε W k0) ψ)‖≤((n:ℝ)^3)⁻¹ :=
    le_of_not_gt (fun h => hgood (Or.inr h))
  have hh₁ : ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearFirstHighWeights d n r ε lam k0) ψ‖≤
      (2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹ :=
    le_of_not_gt (fun h => hgood (Or.inl (Or.inl h)))
  have hh₂ : ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearSecondHighWeights d n r ε lam k0) ψ‖≤
      (2+4*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹ :=
    le_of_not_gt (fun h => hgood (Or.inl (Or.inr h)))
  have hp := radialLinearLow_polar_on_good_event d n ε hn W k0 ψ hg
  dsimp only [radialLinearReadoutPolarControl]
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
theorem radialLinearPauliReadoutPolar_control_eventually (r : ℕ) (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2)
    (hgap : radialLinearEntropy 2 ε<Real.log (2:ℝ)/2) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=4) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ψ∉radialLinearHighSphereBad 2 n r ε lam W k0 ∪ radialLinearLowSphereBad 2 n ε W k0 →
      radialLinearReadoutPolarControl 2 n r ε pauliBasisRecords pauliFullRecord lam W k0 C₁ C₂ ψ := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialLinearHaarReadoutPolar_control_eventually 2 r (by omega) ε hε hhalf hgap lam k0 (by simpa using hcard)
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE] with n hn
  intro W h0 hHS ψ hgood
  have h := hn W h0 hHS ψ hgood
  have hb := (cardinalityHaar_mean_spectrum 2 W k0 h0 hHS (by simpa using hcard) r lam ψ.val).trans
    (cardinalityPauli_mean_spectrum W k0 h0 hHS hcard r lam ψ.val).symm
  have hs := (cardinalityHaar_auxiliary_spectrum 2 W k0 h0 hHS (by simpa using hcard) r lam ψ.val).trans
    (cardinalityPauli_auxiliary_spectrum W k0 h0 hHS hcard r lam ψ.val).symm
  simp only [Fintype.card_fin] at hb hs
  dsimp only [radialLinearReadoutPolarControl] at h ⊢
  rw [hb,hs] at h
  exact h

/-- Actual canonical-sphere probability and simultaneous B/S polar control on its explicit measurable good set. -/
theorem radialLinearHaarReadoutPolar_canonicalSphere_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      MeasurableSet (radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0) ∧
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        (radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0)≤
          ENNReal.ofReal (4*Real.exp (-radialLinearReadoutRate d ε*n)) ∧
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
        ψ∉radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0 →
        radialLinearReadoutPolarControl d n r ε (haarBasisRecords d) id lam W k0 C₁ C₂ ψ := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialLinearHaarReadoutPolar_control_eventually d r hd ε hε hhalf hgap lam k0 hcard
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE,radialLinearHighLow_canonicalSphere_joint_tail d r hd ε hε hhalf hgap lam k0 hcard] with n hc ht
  intro W h0 hW hHS
  exact ⟨(radialLinearHighSphereBad_measurable d n r ε lam W k0).union
    (radialLinearLowSphereBad_measurable d n ε W k0),ht W h0 hW hHS,hc W h0 hHS⟩

/-- Genuine full-Haar sampling of the state gives actual full-Haar reference-record B/S control.
The threshold is uniform in the local family and initial state; each probability is for that fixed family. -/
theorem radialLinearHaarReadoutPolar_haar_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0} ∧
      complexUnitaryHaar (QuditIndex d n) {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0}≤
          ENNReal.ofReal (4*Real.exp (-radialLinearReadoutRate d ε*n)) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex d n) U ψ∉
        radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0 →
        radialLinearReadoutPolarControl d n r ε (haarBasisRecords d) id lam W k0 C₁ C₂
          (complexUnitarySphereAction (QuditIndex d n) U ψ) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialLinearHaarReadoutPolar_control_eventually d r hd ε hε hhalf hgap lam k0 hcard
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE,radialLinearHighLow_haar_joint_tail d r hd ε hε hhalf hgap lam k0 hcard] with n hc ht
  intro W h0 hW hHS ψ
  have hm := (radialLinearHighSphereBad_measurable d n r ε lam W k0).union
    (radialLinearLowSphereBad_measurable d n ε W k0)
  exact ⟨(complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm,
    ht W h0 hW hHS ψ,fun U hU => hc W h0 hHS _ hU⟩

/-- The same genuine full-Haar state event controls both actual finite-Pauli reference-record operators. -/
theorem radialLinearPauliReadoutPolar_haar_eventually (r : ℕ) (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2)
    (hgap : radialLinearEntropy 2 ε<Real.log (2:ℝ)/2) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=4) :
    ∃ C₁ C₂ : ℝ,0<C₁ ∧ 0<C₂ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin 2) (Fin 2) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialLinearHighSphereBad 2 n r ε lam W k0 ∪ radialLinearLowSphereBad 2 n ε W k0} ∧
      complexUnitaryHaar (QuditIndex 2 n) {U | complexUnitarySphereAction (QuditIndex 2 n) U ψ∈
        radialLinearHighSphereBad 2 n r ε lam W k0 ∪ radialLinearLowSphereBad 2 n ε W k0}≤
          ENNReal.ofReal (4*Real.exp (-radialLinearReadoutRate 2 ε*n)) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex 2 n) U ψ∉
        radialLinearHighSphereBad 2 n r ε lam W k0 ∪ radialLinearLowSphereBad 2 n ε W k0 →
        radialLinearReadoutPolarControl 2 n r ε pauliBasisRecords pauliFullRecord lam W k0 C₁ C₂
          (complexUnitarySphereAction (QuditIndex 2 n) U ψ) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialLinearPauliReadoutPolar_control_eventually r ε hε hhalf hgap lam k0 hcard
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  filter_upwards [hE,radialLinearHighLow_haar_joint_tail 2 r (by omega) ε hε hhalf hgap lam k0 (by simpa using hcard)] with n hc ht
  intro W h0 hW hHS ψ
  have hm := (radialLinearHighSphereBad_measurable 2 n r ε lam W k0).union
    (radialLinearLowSphereBad_measurable 2 n ε W k0)
  exact ⟨(complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm,
    ht W h0 hW hHS ψ,fun U hU => hc W h0 hHS _ hU⟩

end CertificationGaussian
