import LocalCertification.Quantum.RadialWeylScore
import CertificationGaussian.ReadoutFullControl
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter CertificationGaussian LocalCertification.Extremal
open scoped BigOperators ENNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
noncomputable section
namespace LocalCertification.Quantum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A genuine self-adjoint operator error gives both Loewner error bounds. -/
theorem hermitian_norm_error_order (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (ε : ℝ) (he : ‖A‖≤ε) :
    -(ε • (1 : Matrix I I ℂ))≤A ∧ A≤ε • (1 : Matrix I I ℂ) := by
  have hn : (‖A‖ : ℝ) • (1 : Matrix I I ℂ)≤ε • (1 : Matrix I I ℂ) := by
    exact smul_le_smul_of_nonneg_right he zero_le_one
  have hlo := hA.isSelfAdjoint.neg_algebraMap_norm_le_self
  have hhi := hA.isSelfAdjoint.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at hlo hhi
  exact ⟨(neg_le_neg hn).trans hlo,hhi.trans hn⟩

/-- The same actual compact-record first and full second moments are Hermitian. -/
theorem cardinalityReadout_moments_hermitian {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (d n r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    (cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.ofLp).IsHermitian ∧
    (cardinalityReadoutSecond d μ record r lam ((d:ℝ)^n) ψ.ofLp).IsHermitian := by
  have hs (ω : Fin n → Ω) :
      IsSelfAdjoint (readoutCenteredScore (cardinalityReadoutKernel d record r lam)
        (cardinalityReadoutTraceScale d n r lam) ((d:ℝ)^n) ψ.ofLp ω) := by
    rw [← cardinalityScore_ofReal d n r record lam ψ ω]
    simp only [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
  have hp (ω : Fin n → Ω) : (productRecordedProjector d record ω).IsHermitian :=
    (productRecordedProjector_posSemidef d record ω).isHermitian
  have hc : Continuous (readoutCenteredScore (cardinalityReadoutKernel d record r lam)
      (cardinalityReadoutTraceScale d n r lam) ((d:ℝ)^n) ψ.ofLp) :=
    readoutCenteredScore_continuous _ (finiteComplementKernel_continuous d record hr _ _)
    (cardinalityReadoutTraceScale d n r lam) ((d:ℝ)^n) ψ.ofLp
  constructor
  · unfold cardinalityReadoutMean readoutMeanOperator
    simp only [Fintype.card_fin]
    apply Matrix.IsHermitian.smul _ (show IsSelfAdjoint ((d:ℝ)^n) from rfl)
    apply hermitian_matrix_integral _ _ (hc.smul (productRecordedProjector_continuous d record hr))
    intro ω
    exact (hp ω).smul (hs ω)
  · unfold cardinalityReadoutSecond readoutSecondOperator
    simp only [Fintype.card_fin]
    apply Matrix.IsHermitian.smul _ (show IsSelfAdjoint ((d:ℝ)^n) from rfl)
    apply hermitian_matrix_integral _ _ ((hc.pow 2).smul (productRecordedProjector_continuous d record hr))
    intro ω
    exact (hp ω).smul ((hs ω).pow 2)

/-- Add an actual Hermitian approximation back to the two-sided operator error. -/
theorem hermitian_approximation_order (A B : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ε : ℝ) (he : ‖B-A‖≤ε) :
    A-ε • (1 : Matrix I I ℂ)≤B ∧ B≤A+ε • (1 : Matrix I I ℂ) := by
  have h := hermitian_norm_error_order (B-A) (hB.sub hA) ε he
  constructor
  · convert add_le_add (le_refl A) h.1 using 1 <;> abel
  · convert add_le_add (le_refl A) h.2 using 1; abel

omit [Fintype I] [DecidableEq I] in
theorem real_diagonal_compression_hermitian {J : Type*} [Fintype J] [DecidableEq J]
    (Q : Matrix I J ℂ) (c : J → ℝ) :
    (Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose Q
    (Matrix.isHermitian_diagonal_iff.mpr (fun j => by
      simp only [IsSelfAdjoint,Complex.star_def,Complex.conj_ofReal]))

/-- Changing the corrected target projector changes each affine envelope by exactly 1-v. -/
theorem affine_target_error (P T : Matrix I I ℂ) (v τ : ℝ) (h : ‖P-T‖≤τ) :
    ‖(P+v • (1-P))-(T+v • (1-T))‖≤|1-v| *τ := by
  have he : (P+v • (1-P))-(T+v • (1-T))=(1-v) • (P-T) := by
    simp only [sub_smul,smul_sub,one_smul]
    abel
  rw [he,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The original pure-target Loewner envelopes follow from the same genuine low isometry. -/
theorem spectral_score_mean_loewner {J : Type*} [Fintype J] [DecidableEq J]
    (ψ : QIT.PureVector I) (Q : Matrix I J ℂ) (hQ : Qᴴ*Q=1)
    (i : J) (c : J → ℝ) (hc : c i=1) (l u ε τ : ℝ)
    (hl0 : l≤0) (hu0 : 0≤u)
    (hcl : ∀ j,j≠i → l≤c j) (hcu : ∀ j,j≠i → c j≤u)
    (B : Matrix I I ℂ) (hBH : B.IsHermitian)
    (hB : ‖B-Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ‖≤ε)
    (hP : ‖Q*Matrix.single i i (1:ℂ)*Qᴴ-ψ.state.matrix‖≤τ) :
    ψ.state.matrix+l • (1-ψ.state.matrix)-(ε+|1-l| *τ) • (1 : Matrix I I ℂ)≤B ∧
    B≤ψ.state.matrix+u • (1-ψ.state.matrix)+(ε+|1-u| *τ) • (1 : Matrix I I ℂ) := by
  let P := Q*Matrix.single i i (1:ℂ)*Qᴴ
  let A := Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ
  have hPH : P.IsHermitian := by
    dsimp only [P]
    rw [isometry_selected_column]
    apply Matrix.ext
    intro a b
    simp [Matrix.conjTranspose_apply,Matrix.vecMulVec,mul_comm]
  have hT := ψ.state.pos.isHermitian
  have hAff (X : Matrix I I ℂ) (hX : X.IsHermitian) (v : ℝ) :
      (X+v • (1-X)).IsHermitian :=
    hX.add ((Matrix.isHermitian_one.sub hX).smul (show IsSelfAdjoint v from rfl))
  have he := isometry_diagonal_envelopes Q hQ i c hc l u hl0 hu0 hcl hcu
  have hb := hermitian_approximation_order A B (real_diagonal_compression_hermitian Q c) hBH ε hB
  have hl := hermitian_approximation_order (ψ.state.matrix+l • (1-ψ.state.matrix))
    (P+l • (1-P)) (hAff _ hT l) (hAff _ hPH l) (|1-l| *τ) (affine_target_error _ _ l τ hP)
  have hu := hermitian_approximation_order (ψ.state.matrix+u • (1-ψ.state.matrix))
    (P+u • (1-P)) (hAff _ hT u) (hAff _ hPH u) (|1-u| *τ) (affine_target_error _ _ u τ hP)
  constructor
  · have hh := sub_le_sub_right (hl.1.trans he.1) (ε • (1 : Matrix I I ℂ))
    have hh' := hh.trans hb.1
    convert hh' using 1
    simp only [add_smul]
    abel
  · have hh := add_le_add (he.2.trans hu.2) (le_refl (ε • (1 : Matrix I I ℂ)))
    have hh' := hb.2.trans hh
    convert hh' using 1
    simp only [add_smul]
    abel

/-- Nonnegative low second coefficients give the missing lower bound as well as the full upper bound. -/
theorem spectral_score_second_loewner {J : Type*} [Fintype J] [DecidableEq J]
    (Q : Matrix I J ℂ) (hQ : Qᴴ*Q=1) (c : J → ℝ) (E ν ε : ℝ)
    (hE : 0≤E) (hc0 : ∀ j,0≤c j) (hcE : ∀ j,c j≤E)
    (M : Matrix I I ℂ) (hMH : M.IsHermitian)
    (hM : ‖M-(ν • (1 : Matrix I I ℂ)+Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ)‖≤ε) :
    (ν-ε) • (1 : Matrix I I ℂ)≤M ∧ M≤(ν+E+ε) • (1 : Matrix I I ℂ) := by
  let A := Q*Matrix.diagonal (fun j => (c j:ℂ))*Qᴴ
  have ha0 : 0≤A := by
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hd : (Matrix.diagonal (fun j => (c j:ℂ))).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro j
      change (0:ℂ)≤(c j:ℂ)
      simpa only [Complex.nonneg_iff,Complex.ofReal_re,Complex.ofReal_im,and_true] using hc0 j
    exact hd.mul_mul_conjTranspose_same Q
  have haE := isometry_diagonal_upper Q hQ c E hE hcE
  have hAH : (ν • (1 : Matrix I I ℂ)+A).IsHermitian :=
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint ν from rfl)).add
      (real_diagonal_compression_hermitian Q c)
  have h := hermitian_approximation_order _ M hAH hMH ε hM
  constructor
  · have hh := sub_le_sub_right (add_le_add (le_refl (ν • (1 : Matrix I I ℂ))) ha0)
      (ε • (1 : Matrix I I ℂ))
    convert hh.trans h.1 using 1
    simp only [add_zero,sub_smul]
  · have hh := add_le_add (add_le_add (le_refl (ν • (1 : Matrix I I ℂ))) haE)
      (le_refl (ε • (1 : Matrix I I ℂ)))
    convert h.2.trans hh using 1
    simp only [add_smul]

/-- The four original operator inequalities, for the genuine reference-record B and full M. -/
def completeReadoutLoewner {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (E η ε : ℝ) (ψ : QIT.PureVector (QuditIndex d n)) : Prop :=
  let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let B := cardinalityReadoutMean d μ record r lam ((d:ℝ)^n) ψ.amp
  let M := cardinalityReadoutSecond d μ record r lam ((d:ℝ)^n) ψ.amp
  let ν := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)
  ψ.state.matrix+l • (1-ψ.state.matrix)-η • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)≤B ∧
  B≤ψ.state.matrix+u • (1-ψ.state.matrix)+η • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) ∧
  (ν-ε) • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)≤M ∧
  M≤(ν+E+ε) • (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)

/-- A single fixed deterministic constant accommodates both affine target-envelope errors. -/
def completeMeanConstant (d r : ℕ) (lam : ℕ → ℝ) (C : ℝ) : ℝ :=
  C+2*(|1-lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)|+
    |1-upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)|)

/-- No alternate low family is introduced: this consumes the original actual full-readout event. -/
theorem completeReadoutLoewner_of_full_control {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (d n r : ℕ) (hd : 0<d) [NeZero d] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (lam : ℕ → ℝ) (h0 : lam 0=1) (E : ℝ) (hE : 0≤E)
    (he : ∀ w,radialSecondCoefficient d r lam w≤E)
    (C₁ C₂ CM : ℝ) (ψ : QIT.PureVector (QuditIndex d n))
    (h : radialReadoutFullControl d n r μ record lam localWeylFin 0 C₁ C₂ CM
      (WithLp.toLp 2 ψ.amp)) :
    completeReadoutLoewner d n r μ record lam E
      (completeMeanConstant d r lam C₁*((n:ℝ)^3)⁻¹) ((C₂+CM)*((n:ℝ)^3)⁻¹) ψ := by
  let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let t := ((n:ℝ)^3)⁻¹
  let Q := radialWeylPolarMatrix r (WithLp.toLp 2 ψ.amp)
  let c : RadialWeylIndex d n r → ℝ := fun w => radialFirstCoefficient d r lam (weylWeight w.val)
  let e : RadialWeylIndex d n r → ℝ := fun w => radialSecondCoefficient d r lam (weylWeight w.val)
  have hq : 1<(d:ℝ)+1 := by exact_mod_cast Nat.lt_add_one_iff.mpr hd
  have hh := cardinalityReadout_moments_hermitian d n r μ record hr lam (WithLp.toLp 2 ψ.amp)
  have hc := radialWeyl_coefficients (d:=d) (n:=n) r lam h0 hd
  have hm := spectral_score_mean_loewner ψ Q h.1.1 (radialWeylIdentity d n r) c hc.1 l u
    (C₁*t) (2*t) (envelope_zero_bounds _ hq _).1 (envelope_zero_bounds _ hq _).2
    (fun w hw => (hc.2 w hw).1) (fun w hw => (hc.2 w hw).2) _ hh.1
    (radialWeyl_first_matrix_error r μ record lam C₁ C₂ _ h.1)
    (radialWeyl_target_projector r μ record lam C₁ C₂ ψ h.1)
  have hrem := h.2.1
  simp only [cardinalityReadoutSecondError,sub_sub] at hrem
  rw [← Matrix.cstar_norm_def] at hrem
  have hfull := radialWeyl_full_matrix_error r μ record lam C₁ C₂ CM
    (cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)) _ h.1 hrem
  have hs := spectral_score_second_loewner Q h.1.1 e E
    (cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)) ((C₂+CM)*t) hE
    (fun w => radialSecondCoefficient_nonneg d r _ lam) (fun w => he _) _ hh.2 hfull
  have ht : 0≤t := by dsimp only [t]; positivity
  have hL : C₁*t+|1-l| *(2*t)≤completeMeanConstant d r lam C₁*t := by
    dsimp only [completeMeanConstant,l,u]
    nlinarith [mul_nonneg (abs_nonneg (1-upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))) ht]
  have hU : C₁*t+|1-u| *(2*t)≤completeMeanConstant d r lam C₁*t := by
    dsimp only [completeMeanConstant,l,u]
    nlinarith [mul_nonneg (abs_nonneg (1-lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))) ht]
  refine ⟨?_,?_,hs.1,hs.2⟩
  · exact (sub_le_sub_left (smul_le_smul_of_nonneg_right hL zero_le_one) _).trans hm.1
  · exact hm.2.trans (add_le_add (le_refl _) (smul_le_smul_of_nonneg_right hU zero_le_one))


/-- The exact supremum e_* in the original uniform second-moment statement. -/
def radialSecondCoefficientSup (d r : ℕ) (lam : ℕ → ℝ) : ℝ :=
  sSup (Set.range (radialSecondCoefficient d r lam))

theorem radialSecondCoefficientSup_bounds (d r : ℕ) (hd : 1≤d)
    (lam : ℕ → ℝ) (h0 : lam 0=1) :
    0<radialSecondCoefficientSup d r lam ∧
      ∀ w,|radialSecondCoefficient d r lam w|≤radialSecondCoefficientSup d r lam := by
  obtain ⟨C,_hC,hC⟩ := radialSecondCoefficient_bounded d r hd lam
  have hb : BddAbove (Set.range (radialSecondCoefficient d r lam)) :=
    ⟨C,by rintro _ ⟨w,rfl⟩; exact (le_abs_self _).trans (hC w)⟩
  have hw (w : ℕ) : radialSecondCoefficient d r lam w≤radialSecondCoefficientSup d r lam :=
    le_csSup hb (Set.mem_range_self w)
  have hz : radialSecondCoefficient d r lam 0=2 := by
    simp only [radialSecondCoefficient,radialFirstCoefficient_zero,h0,one_pow,mul_one]
  constructor
  · have h := hw 0
    rw [hz] at h
    linarith
  · intro w
    rw [abs_of_nonneg (radialSecondCoefficient_nonneg d r w lam)]
    exact hw w

/-- Original uniform score bounds for full local Haar readout, including the second-moment lower side.
The event and all constants precede every unknown input and every requested testing error. -/
theorem completeHaarReadout_loewner_eventually (d r : ℕ) (hd : 3≤d) [NeZero d]
    (lam : ℕ → ℝ) (h0 : lam 0=1) :
    ∃ E Cη Cε Cbad : ℝ,0<E ∧ 0<Cη ∧ 0<Cε ∧ 0<Cbad ∧ E=radialSecondCoefficientSup d r lam ∧
      (∀ w,0≤radialSecondCoefficient d r lam w ∧ radialSecondCoefficient d r lam w≤E) ∧
      ∀ᶠ n : ℕ in atTop,∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (Cbad*((n:ℝ)^8)⁻¹) ∧
        ∀ U,U∉bad → completeReadoutLoewner d n r (haarBasisRecords d) id lam E
          (Cη*((n:ℝ)^3)⁻¹) (Cε*((n:ℝ)^3)⁻¹) (haarPureVector ψ₀ U) := by
  let E := radialSecondCoefficientSup d r lam
  obtain ⟨hE,he⟩ := radialSecondCoefficientSup_bounds d r (by omega) lam h0
  obtain ⟨C₁,C₂,CM,hC₁,hC₂,hCM,hEvent⟩ := radialHaar_full_readout_haar_eventually
    d r hd lam (0 : ZMod d × ZMod d) localWeylLabel_card
  let Cbad := radialHighGaussianConstant d r lam+
    2*radialHighGaussianConstant d r (fun j => (lam j)^2)+3
  have hbad : 0<Cbad := by
    have ha := radialHighGaussianConstant_pos d r (by omega) lam
    have hb := radialHighGaussianConstant_pos d r (by omega) (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  refine ⟨E,completeMeanConstant d r lam C₁,C₂+CM,Cbad,hE,?_,by linarith,hbad,rfl,
    fun w => ⟨radialSecondCoefficient_nonneg _ _ _ _,(le_abs_self _).trans (he w)⟩,?_⟩
  · unfold completeMeanConstant
    exact add_pos_of_pos_of_nonneg hC₁ (by positivity)
  · filter_upwards [hEvent] with n hn
    intro ψ₀
    obtain ⟨hm,hp,hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
      localWeylFin_hilbertSchmidt ψ₀
    refine ⟨{U | complexUnitarySphereAction (QuditIndex d n) U ψ₀∈
      radialReadoutFullBad d n r (haarBasisRecords d) id lam localWeylFin 0 CM},hm,hp,?_⟩
    intro U hU
    exact completeReadoutLoewner_of_full_control d n r (by omega) _ id continuous_id lam h0 E hE.le
      (fun w => (le_abs_self _).trans (he w)) C₁ C₂ CM (haarPureVector ψ₀ U) (hc U hU)

/-- The same full operator conclusion for the actual finite Pauli records at d=2. -/
theorem completePauliReadout_loewner_eventually (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0=1) :
    ∃ E Cη Cε Cbad : ℝ,0<E ∧ 0<Cη ∧ 0<Cε ∧ 0<Cbad ∧ E=radialSecondCoefficientSup 2 r lam ∧
      (∀ w,0≤radialSecondCoefficient 2 r lam w ∧ radialSecondCoefficient 2 r lam w≤E) ∧
      ∀ᶠ n : ℕ in atTop,∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex 2 n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex 2 n) bad≤ENNReal.ofReal (Cbad*((n:ℝ)^8)⁻¹) ∧
        ∀ U,U∉bad → completeReadoutLoewner 2 n r pauliBasisRecords pauliFullRecord lam E
          (Cη*((n:ℝ)^3)⁻¹) (Cε*((n:ℝ)^3)⁻¹) (haarPureVector ψ₀ U) := by
  let E := radialSecondCoefficientSup 2 r lam
  obtain ⟨hE,he⟩ := radialSecondCoefficientSup_bounds 2 r (by omega) lam h0
  obtain ⟨C₁,C₂,CM,hC₁,hC₂,hCM,hEvent⟩ := radialPauli_full_readout_haar_eventually
    r lam (0 : ZMod 2 × ZMod 2) localWeylLabel_card
  let Cbad := radialHighGaussianConstant 2 r lam+
    2*radialHighGaussianConstant 2 r (fun j => (lam j)^2)+3
  have hbad : 0<Cbad := by
    have ha := radialHighGaussianConstant_pos 2 r (by omega) lam
    have hb := radialHighGaussianConstant_pos 2 r (by omega) (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  refine ⟨E,completeMeanConstant 2 r lam C₁,C₂+CM,Cbad,hE,?_,by linarith,hbad,rfl,
    fun w => ⟨radialSecondCoefficient_nonneg _ _ _ _,(le_abs_self _).trans (he w)⟩,?_⟩
  · unfold completeMeanConstant
    exact add_pos_of_pos_of_nonneg hC₁ (by positivity)
  · filter_upwards [hEvent] with n hn
    intro ψ₀
    obtain ⟨hm,hp,hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
      localWeylFin_hilbertSchmidt ψ₀
    refine ⟨{U | complexUnitarySphereAction (QuditIndex 2 n) U ψ₀∈
      radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam localWeylFin 0 CM},hm,hp,?_⟩
    intro U hU
    exact completeReadoutLoewner_of_full_control 2 n r (by omega) _ pauliFullRecord
      continuous_of_discreteTopology lam h0 E hE.le (fun w => (le_abs_self _).trans (he w))
      C₁ C₂ CM (haarPureVector ψ₀ U) (hc U hU)

/-- The deterministic operator errors converge to zero with the original n^-3 rate. -/
theorem completeReadout_error_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*((n:ℝ)^3)⁻¹) atTop (nhds 0) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).pow 3
  simpa only [Function.comp_apply,inv_pow,zero_pow (by omega : 3≠0),mul_zero] using
    tendsto_const_nhds.mul h

theorem completeReadout_failure_le_inverse_square (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,C*((n:ℝ)^8)⁻¹≤((n:ℝ)^2)⁻¹ := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).pow 6
  have hc : Tendsto (fun n : ℕ => C*(n:ℝ)⁻¹^6) atTop (nhds 0) := by
    simpa only [Function.comp_apply,zero_pow (by omega : 6≠0),mul_zero] using tendsto_const_nhds.mul h
  filter_upwards [hc.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn
  rw [← inv_pow,← inv_pow]
  calc
    C*(n:ℝ)⁻¹^8=(C*(n:ℝ)⁻¹^6)*(n:ℝ)⁻¹^2 := by ring
    _≤1*(n:ℝ)⁻¹^2 := mul_le_mul_of_nonneg_right hn.le (sq_nonneg _)
    _=_ := one_mul _

/-- Haar score bounds with second-moment envelope e_* and inverse-square exceptional probability.
For each sufficiently large n and reference vector ψ₀, one exceptional set controls both operators.
Both deterministic errors tend to zero. -/
theorem completeHaarReadout_scorebounds (d r : ℕ) (hd : 3≤d) [NeZero d]
    (lam : ℕ → ℝ) (h0 : lam 0=1) :
    ∃ η ε : ℕ → ℝ,(∀ n,0≤η n ∧ 0≤ε n) ∧
      Tendsto η atTop (nhds 0) ∧ Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
        ∀ U,U∉bad → completeReadoutLoewner d n r (haarBasisRecords d) id lam
          (radialSecondCoefficientSup d r lam) (η n) (ε n) (haarPureVector ψ₀ U) := by
  obtain ⟨E,Cη,Cε,Cbad,_hE,hη,hε,_hbad,hEeq,_he,hN⟩ :=
    completeHaarReadout_loewner_eventually d r hd lam h0
  subst E
  refine ⟨fun n => Cη*((n:ℝ)^3)⁻¹,fun n => Cε*((n:ℝ)^3)⁻¹,
    fun n => ⟨by positivity,by positivity⟩,completeReadout_error_tendsto_zero Cη,
    completeReadout_error_tendsto_zero Cε,?_⟩
  filter_upwards [hN,completeReadout_failure_le_inverse_square Cbad] with n hn hp
  intro ψ₀
  obtain ⟨bad,hm,hb,hc⟩ := hn ψ₀
  exact ⟨bad,hm,hb.trans (ENNReal.ofReal_le_ofReal hp),hc⟩

theorem completePauliReadout_scorebounds (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0=1) :
    ∃ η ε : ℕ → ℝ,(∀ n,0≤η n ∧ 0≤ε n) ∧
      Tendsto η atTop (nhds 0) ∧ Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex 2 n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex 2 n) bad≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
        ∀ U,U∉bad → completeReadoutLoewner 2 n r pauliBasisRecords pauliFullRecord lam
          (radialSecondCoefficientSup 2 r lam) (η n) (ε n) (haarPureVector ψ₀ U) := by
  obtain ⟨E,Cη,Cε,Cbad,_hE,hη,hε,_hbad,hEeq,_he,hN⟩ :=
    completePauliReadout_loewner_eventually r lam h0
  subst E
  refine ⟨fun n => Cη*((n:ℝ)^3)⁻¹,fun n => Cε*((n:ℝ)^3)⁻¹,
    fun n => ⟨by positivity,by positivity⟩,completeReadout_error_tendsto_zero Cη,
    completeReadout_error_tendsto_zero Cε,?_⟩
  filter_upwards [hN,completeReadout_failure_le_inverse_square Cbad] with n hn hp
  intro ψ₀
  obtain ⟨bad,hm,hb,hc⟩ := hn ψ₀
  exact ⟨bad,hm,hb.trans (ENNReal.ofReal_le_ofReal hp),hc⟩

end LocalCertification.Quantum
