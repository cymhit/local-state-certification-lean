import CertificationGaussian.RadialLinearReadoutPolar
import CertificationGaussian.ReadoutFullSecondControl

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The genuine polar compression is bounded by the original diagonal sup bound, including empty low spaces. -/
theorem radialLinearPolarCompression_norm_le (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (a : (Fin n → K) → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (M : ℝ) (hM : 0≤M) (ha : ∀ w∈radialLinearLowLabels ε n k0,|a w|≤M)
    (hQ : ∀ x,‖rectangularEuclideanCLM
      (matrixPolarCorrection (unitaryOrbitMatrix (radialLinearLowOrbitFamily d n ε W k0) ψ)) x‖=‖x‖) :
    ‖radialLinearPolarCompression d n ε W k0 a ψ‖≤M := by
  let Q := matrixPolarCorrection (unitaryOrbitMatrix (radialLinearLowOrbitFamily d n ε W k0) ψ)
  have hqn : ‖Q‖≤1 := by
    change ‖rectangularEuclideanCLM Q‖≤1
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by rw [hQ]; simp)
  have hdn := orbitLowDiagonal_norm_le a (radialLinearLowLabels ε n k0) M hM ha
  unfold radialLinearPolarCompression
  dsimp only
  change ‖Q*Matrix.diagonal (fun w : radialLinearLowLabels ε n k0 => (a w.val:ℂ))*Qᴴ‖≤M
  calc
    _ ≤ ‖Q‖*‖Matrix.diagonal (fun w : radialLinearLowLabels ε n k0 => (a w.val:ℂ))‖*‖Qᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1*M*1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = M := by ring

/-- Actual B/S norm bounds follow from the concrete polar-control conclusion; no moment hypothesis is introduced. -/
theorem radialLinearReadoutPolarControl_norm_bounds {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (hn : 1≤n) (ε : ℝ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (C₁ C₂ M₁ M₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (h₁ : ∀ w∈radialLinearLowLabels ε n k0,
      |radialFirstCoefficient d r lam (radialBellSupport k0 w).card|≤M₁)
    (h₂ : ∀ w∈radialLinearLowLabels ε n k0,
      |radialSecondCoefficient d r lam (radialBellSupport k0 w).card|≤M₂)
    (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (hc : radialLinearReadoutPolarControl d n r ε μ record lam W k0 C₁ C₂ ψ) :
    ‖rectangularEuclideanCLM (cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.ofLp)‖≤M₁+C₁ ∧
    ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary d μ record r lam ((d:ℝ)^n) ψ.ofLp)‖≤M₂+C₂ := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have ht : ((n:ℝ)^3)⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ hn')
  have hp₁ := radialLinearPolarCompression_norm_le d n ε W k0
    (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ M₁ hM₁ h₁ hc.2.2.1
  have hp₂ := radialLinearPolarCompression_norm_le d n ε W k0
    (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ M₂ hM₂ h₂ hc.2.2.1
  constructor
  · have h := (norm_le_norm_sub_add _ _).trans (add_le_add hc.2.2.2.1 hp₁)
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hC₁])
  · have h := (norm_le_norm_sub_add _ _).trans (add_le_add hc.2.2.2.2 hp₂)
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hC₂])

/-- Uniform actual full-Haar B/S norm bounds on the same explicit sphere good event. -/
theorem radialLinearHaarReadout_norm_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ Kb Ks : ℝ,0<Kb ∧ 0<Ks ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ψ∉radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0 →
      ‖rectangularEuclideanCLM (cardinalityReadoutMean d (haarBasisRecords d) id r lam ((d:ℝ)^n) ψ.val.ofLp)‖≤Kb ∧
      ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary d (haarBasisRecords d) id r lam ((d:ℝ)^n) ψ.val.ofLp)‖≤Ks := by
  obtain ⟨M₁,hM₁,hm₁⟩ := radialFirstCoefficient_bounded d r (by omega) lam
  obtain ⟨M₂,hM₂,hm₂⟩ := radialFirstCoefficient_bounded d r (by omega) (fun j => (lam j)^2)
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialLinearHaarReadoutPolar_control_eventually d r hd ε hε hhalf hgap lam k0 hcard
  refine ⟨M₁+C₁,2*M₂+C₂,by positivity,by positivity,?_⟩
  filter_upwards [hE,eventually_ge_atTop 1] with n he hn
  intro W h0 hHS ψ hg
  apply radialLinearReadoutPolarControl_norm_bounds d n r hn ε (haarBasisRecords d) id lam W k0
    C₁ C₂ M₁ (2*M₂) hC₁.le hC₂.le hM₁.le (by positivity)
    (fun w _ => hm₁ _) _ ψ (he W h0 hHS ψ hg)
  intro w _
  simp only [radialSecondCoefficient,abs_mul,abs_of_pos (show (0:ℝ)<2 by norm_num)]
  exact mul_le_mul_of_nonneg_left (hm₂ _) (by norm_num)

/-- The actual finite-Pauli B/S norm bounds use the same true spectral operators. -/
theorem radialLinearPauliReadout_norm_eventually (r : ℕ) (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2)
    (hgap : radialLinearEntropy 2 ε<Real.log (2:ℝ)/2) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=4) :
    ∃ Kb Ks : ℝ,0<Kb ∧ 0<Ks ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ψ∉radialLinearHighSphereBad 2 n r ε lam W k0 ∪ radialLinearLowSphereBad 2 n ε W k0 →
      ‖rectangularEuclideanCLM (cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam ((2:ℝ)^n) ψ.val.ofLp)‖≤Kb ∧
      ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord r lam ((2:ℝ)^n) ψ.val.ofLp)‖≤Ks := by
  obtain ⟨Kb,Ks,hKb,hKs,hE⟩ := radialLinearHaarReadout_norm_eventually 2 r (by omega) ε hε hhalf hgap lam k0 (by simpa using hcard)
  refine ⟨Kb,Ks,hKb,hKs,?_⟩
  filter_upwards [hE] with n hn
  intro W h0 hHS ψ hg
  have h := hn W h0 hHS ψ hg
  have hb := (cardinalityHaar_mean_spectrum 2 W k0 h0 hHS (by simpa using hcard) r lam ψ.val).trans
    (cardinalityPauli_mean_spectrum W k0 h0 hHS hcard r lam ψ.val).symm
  have hs := (cardinalityHaar_auxiliary_spectrum 2 W k0 h0 hHS (by simpa using hcard) r lam ψ.val).trans
    (cardinalityPauli_auxiliary_spectrum W k0 h0 hHS hcard r lam ψ.val).symm
  simp only [Fintype.card_fin] at hb hs
  rw [hb,hs] at h
  exact h

/-- All B/S and trace-scale hypotheses in the actual full-Haar second-moment radius estimate are discharged.
Only the original explicit high/low, common-radius, and true remainder good events remain. -/
theorem radialLinearHaar_full_second_control_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∀ x : Fin 2 × QuditIndex d n → ℝ,
      sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)∉
        radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0 →
      |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹ →
      ‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
        (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖≤((n:ℝ)^3)⁻¹ →
      cardinalityReadoutSecondError d n r (haarBasisRecords d) id lam
        (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x))≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨Kb,Ks,hKb,hKs,hE⟩ := radialLinearHaarReadout_norm_eventually d r hd ε hε hhalf hgap lam k0 hcard
  let A := complementLambdaCoefficient d r lam
  let An := complementLambdaCoefficient d r (fun j => (lam j)^2)
  have hA : 0≤A := complementLambdaCoefficient_nonneg d r (by omega) lam
  have hAn : 0≤An := complementLambdaCoefficient_nonneg d r (by omega) _
  refine ⟨2*Ks+4+4*A*Kb+4*(An+A^2),by positivity,?_⟩
  filter_upwards [hE,eventually_ge_atTop 2] with n he hn
  intro W h0 hHS e₀ x hgood hr hZ
  have hnorm := he W h0 hHS (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) hgood
  have h := cardinalityHaar_second_error_of_good_radius d n r hd hn lam Kb Ks x e₀ hr hZ hnorm.1 hnorm.2
  exact h.trans (readout_full_error_scalar_le n r (by omega) A An Kb Ks _ _ hA hAn hKb.le hKs.le
    (cardinalityReadoutTraceScale_abs_le d n r (by omega) (by omega) lam)
    (cardinalityReadoutTraceScale_abs_le d n r (by omega) (by omega) _))

/-- The same true full second-moment estimate for the finite-Pauli record law, with no B/S norm premises. -/
theorem radialLinearPauli_full_second_control_eventually (r : ℕ) (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2)
    (hgap : radialLinearEntropy 2 ε<Real.log (2:ℝ)/2) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=4) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ∀ x : Fin 2 × QuditIndex 2 n → ℝ,
      sphereDirection e₀ (complexGaussianLift (QuditIndex 2 n) x)∉
        radialLinearHighSphereBad 2 n r ε lam W k0 ∪ radialLinearLowSphereBad 2 n ε W k0 →
      |gaussianRadius (QuditIndex 2 n) x-1|≤((n:ℝ)^(r+4))⁻¹ →
      ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
        (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖≤((n:ℝ)^3)⁻¹ →
      cardinalityReadoutSecondError 2 n r pauliBasisRecords pauliFullRecord lam
        (sphereDirection e₀ (complexGaussianLift (QuditIndex 2 n) x))≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨Kb,Ks,hKb,hKs,hE⟩ := radialLinearPauliReadout_norm_eventually r ε hε hhalf hgap lam k0 hcard
  let A := complementLambdaCoefficient 2 r lam
  let An := complementLambdaCoefficient 2 r (fun j => (lam j)^2)
  have hA : 0≤A := complementLambdaCoefficient_nonneg 2 r (by omega) lam
  have hAn : 0≤An := complementLambdaCoefficient_nonneg 2 r (by omega) _
  refine ⟨2*Ks+4+4*A*Kb+4*(An+A^2),by positivity,?_⟩
  filter_upwards [hE,eventually_ge_atTop 2] with n he hn
  intro W h0 hHS e₀ x hgood hr hZ
  have hnorm := he W h0 hHS (sphereDirection e₀ (complexGaussianLift (QuditIndex 2 n) x)) hgood
  have h := cardinalityPauli_second_error_of_good_radius n r hn lam Kb Ks x e₀ hr hZ hnorm.1 hnorm.2
  exact h.trans (readout_full_error_scalar_le n r (by omega) A An Kb Ks _ _ hA hAn hKb.le hKs.le
    (cardinalityReadoutTraceScale_abs_le 2 n r (by omega) (by omega) lam)
    (cardinalityReadoutTraceScale_abs_le 2 n r (by omega) (by omega) _))

end CertificationGaussian
