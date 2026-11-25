import CertificationGaussian.RadialReadoutPolar
import CertificationGaussian.ReadoutMomentError

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The genuine polar compression is bounded by the original diagonal sup bound, including empty low spaces. -/
theorem radialPolarCompression_norm_le (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (a : (Fin n → K) → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (M : ℝ) (hM : 0≤M) (ha : ∀ w∈radialLowLabels (S:=Fin n) d r k0,|a w|≤M)
    (hQ : ∀ x,‖rectangularEuclideanCLM
      (matrixPolarCorrection (unitaryOrbitMatrix (radialLowOrbitFamily d n r W k0) ψ)) x‖=‖x‖) :
    ‖radialPolarCompression d n r W k0 a ψ‖≤M := by
  let Q := matrixPolarCorrection (unitaryOrbitMatrix (radialLowOrbitFamily d n r W k0) ψ)
  have hqn : ‖Q‖≤1 := by
    change ‖rectangularEuclideanCLM Q‖≤1
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by rw [hQ]; simp)
  have hdn := orbitLowDiagonal_norm_le a (radialLowLabels (S:=Fin n) d r k0) M hM ha
  unfold radialPolarCompression
  dsimp only
  change ‖Q*Matrix.diagonal (fun w : radialLowLabels (S:=Fin n) d r k0 => (a w.val:ℂ))*Qᴴ‖≤M
  calc
    _ ≤ ‖Q‖*‖Matrix.diagonal (fun w : radialLowLabels (S:=Fin n) d r k0 => (a w.val:ℂ))‖*‖Qᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1*M*1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = M := by ring

/-- Actual B/S norm bounds follow from the concrete polar-control conclusion; no moment hypothesis is introduced. -/
theorem radialReadoutPolarControl_norm_bounds {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (hn : 1≤n) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (C₁ C₂ M₁ M₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (h₁ : ∀ w∈radialLowLabels (S:=Fin n) d r k0,
      |radialFirstCoefficient d r lam (radialBellSupport k0 w).card|≤M₁)
    (h₂ : ∀ w∈radialLowLabels (S:=Fin n) d r k0,
      |radialSecondCoefficient d r lam (radialBellSupport k0 w).card|≤M₂)
    (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (hc : radialReadoutPolarControl d n r μ record lam W k0 C₁ C₂ ψ) :
    ‖rectangularEuclideanCLM (cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.ofLp)‖≤M₁+C₁ ∧
    ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary d μ record r lam ((d:ℝ)^n) ψ.ofLp)‖≤M₂+C₂ := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have ht : ((n:ℝ)^3)⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ hn')
  have hp₁ := radialPolarCompression_norm_le d n r W k0
    (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ M₁ hM₁ h₁ hc.2.2.1
  have hp₂ := radialPolarCompression_norm_le d n r W k0
    (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ M₂ hM₂ h₂ hc.2.2.1
  constructor
  · have h := (norm_le_norm_sub_add _ _).trans (add_le_add hc.2.2.2.1 hp₁)
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hC₁])
  · have h := (norm_le_norm_sub_add _ _).trans (add_le_add hc.2.2.2.2 hp₂)
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hC₂])

/-- Uniform actual full-Haar B/S norm bounds on the same explicit sphere good event. -/
theorem radialHaarReadout_norm_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ Kb Ks : ℝ,0<Kb ∧ 0<Ks ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ψ∉radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0 →
      ‖rectangularEuclideanCLM (cardinalityReadoutMean d (haarBasisRecords d) id r lam ((d:ℝ)^n) ψ.val.ofLp)‖≤Kb ∧
      ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary d (haarBasisRecords d) id r lam ((d:ℝ)^n) ψ.val.ofLp)‖≤Ks := by
  obtain ⟨M₁,hM₁,hm₁⟩ := radialFirstCoefficient_bounded d r (by omega) lam
  obtain ⟨M₂,hM₂,hm₂⟩ := radialFirstCoefficient_bounded d r (by omega) (fun j => (lam j)^2)
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialHaarReadoutPolar_control_eventually d r hd lam k0 hcard
  refine ⟨M₁+C₁,2*M₂+C₂,by positivity,by positivity,?_⟩
  filter_upwards [hE,eventually_ge_atTop 1] with n he hn
  intro W h0 hHS ψ hg
  apply radialReadoutPolarControl_norm_bounds d n r hn (haarBasisRecords d) id lam W k0
    C₁ C₂ M₁ (2*M₂) hC₁.le hC₂.le hM₁.le (by positivity)
    (fun w _ => hm₁ _) _ ψ (he W h0 hHS ψ hg)
  intro w _
  simp only [radialSecondCoefficient,abs_mul,abs_of_pos (show (0:ℝ)<2 by norm_num)]
  exact mul_le_mul_of_nonneg_left (hm₂ _) (by norm_num)

/-- The actual finite-Pauli B/S norm bounds use the same true spectral operators. -/
theorem radialPauliReadout_norm_eventually (r : ℕ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=4) :
    ∃ Kb Ks : ℝ,0<Kb ∧ 0<Ks ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ψ∉radialHighSphereBad 2 n r lam W k0 ∪ radialLowSphereBad 2 n r W k0 →
      ‖rectangularEuclideanCLM (cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam ((2:ℝ)^n) ψ.val.ofLp)‖≤Kb ∧
      ‖rectangularEuclideanCLM (cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord r lam ((2:ℝ)^n) ψ.val.ofLp)‖≤Ks := by
  obtain ⟨Kb,Ks,hKb,hKs,hE⟩ := radialHaarReadout_norm_eventually 2 r (by omega) lam k0 (by simpa using hcard)
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

end CertificationGaussian
