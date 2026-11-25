import LocalCertification.Protocol.FixedScoreAchievabilityCanonical

/-!
Quantitative fixed-score protocols for the uniform transition in Supplemental Material Section V.C.
The finite-size theorem retains the inverse-cube operator errors and constructs
the actual product-basis protocol with its deterministic cap. These budgets
refer to the existing product-basis protocol class.
-/

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Metric Filter Set CertificationGaussian
  LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Probability
open scoped BigOperators ENNReal Matrix.Norms.L2Operator Topology
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {H : Type u} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]
  [CompactSpace H] [SecondCountableTopology H] {d n : ℕ} [NeZero d]

/-- Explicit finite-size error inequalities give the implemented score test,
including validity on every promised state and a cap on every path. The window
may depend on n because no window-dependent eventual cutoff is used. -/
theorem fixedScore_achievable_of_full_control (hd : 2 ≤ d)
    (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν]
    (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0 = 1) (C₁ C₂ CM E a b : ℝ)
    (hE : 0 ≤ E) (he : ∀ w : ℕ, radialSecondCoefficient d r lam w ≤ E)
    (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hg : 0 < scoreWindowGap
      (lowerEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam))
      (upperEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam)) a b)
    (hL : (C₁ + 2 * |1 - lowerEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam)|) *
      ((n : ℝ)^3)⁻¹ ≤ scoreWindowGap
        (lowerEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam))
        (upperEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam)) a b / 4)
    (hU : (C₁ + 2 * |1 - upperEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam)|) *
      ((n : ℝ)^3)⁻¹ ≤ scoreWindowGap
        (lowerEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam))
        (upperEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam)) a b / 4)
    (hM : (C₂ + CM) * ((n : ℝ)^3)⁻¹ ≤ 1)
    (ψ : QIT.PureVector (QuditIndex d n))
    (hfull : radialReadoutFullControl d n r (ν.prod (uniformFiniteOutcome d))
      (fun p : H × Fin d => (setting p.1, p.2)) lam localWeylFin 0 C₁ C₂ CM
      (WithLp.toLp 2 ψ.amp))
    (δ : ℝ) (hδ : 0 < δ) (hhalf : δ ≤ 1/2) :
    FixedScoreAchievable setting hs ν r lam E a b δ ψ := by
  let l := lowerEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam)
  let u := upperEnvelope ((d : ℝ) + 1) (radialPolynomial d r lam)
  let Δ := scoreWindowGap l u a b
  have hcontrol := hfull.1
  have hrem := hfull.2.1
  simp only [cardinalityReadoutSecondError, sub_sub] at hrem
  rw [← Matrix.cstar_norm_def] at hrem
  let Q := radialWeylPolarMatrix r (WithLp.toLp 2 ψ.amp)
  let c : RadialWeylIndex d n r → ℝ :=
    fun w => radialFirstCoefficient d r lam (weylWeight w.val)
  let e : RadialWeylIndex d n r → ℝ :=
    fun w => radialSecondCoefficient d r lam (weylWeight w.val)
  let nu := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)
  have hq : 1 < (d : ℝ) + 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc := radialWeyl_coefficients (d := d) (n := n) r lam h0 (by omega)
  have hL' : C₁ * ((n : ℝ)^3)⁻¹ + |1-l| * (2 * ((n : ℝ)^3)⁻¹) ≤ Δ/4 := by
    nlinarith [hL]
  have hU' : C₁ * ((n : ℝ)^3)⁻¹ + |1-u| * (2 * ((n : ℝ)^3)⁻¹) ≤ Δ/4 := by
    nlinarith [hU]
  let μ := ν.prod (uniformFiniteOutcome d)
  let record : H × Fin d → ComplexUnitary (Fin d) × Fin d :=
    fun p => (setting p.1, p.2)
  let ψv : EuclideanSpace ℂ (QuditIndex d n) := WithLp.toLp 2 ψ.amp
  have hB := radialWeyl_first_matrix_error (d := d) (n := n) r μ record lam C₁ C₂ ψv hcontrol
  have hsecond := radialWeyl_full_matrix_error (d := d) (n := n)
    r μ record lam C₁ C₂ CM nu ψv hcontrol hrem
  have hP := radialWeyl_target_projector (d := d) (n := n) r μ record lam C₁ C₂ ψ hcontrol
  exact cardinality_achievable_of_spectral_control (d := d) (n := n)
    (J := RadialWeylIndex d n r) setting hs ν r lam ψ Q hcontrol.1
    (radialWeylIdentity d n r) c e hc.1 l u E nu (C₁ * ((n : ℝ)^3)⁻¹)
    ((C₂+CM) * ((n : ℝ)^3)⁻¹) (2 * ((n : ℝ)^3)⁻¹) a b δ
    (envelope_zero_bounds _ hq _).1 (envelope_zero_bounds _ hq _).2 hE
    (squared_traceScale_nonneg d n r (by omega) lam)
    (fun w hw => (hc.2 w hw).1) (fun w hw => (hc.2 w hw).2) (fun w => he _)
    hB hsecond hP ha hb0 hb1 hg hL' hU' hM hδ hhalf

/-- Quantitative operator control and actual capped tests on one compact target
family. The error constants and size cutoff precede every fidelity window. -/
def QuantitativeFixedScoreConclusion (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ) : Prop :=
  ∃ Cη Cε : ℝ, 0 < Cη ∧ 0 < Cε ∧
  ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
    (∀ n, IsCompact (good n)) ∧
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (((n : ℝ)^2)⁻¹) ∧
      ∀ ψ ∈ good n,
        completeReadoutLoewner d n r (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1, p.2)) lam
          (radialSecondCoefficientSup d r lam)
          (Cη * ((n : ℝ)^3)⁻¹) (Cε * ((n : ℝ)^3)⁻¹) (spherePureVector ψ) ∧
        ∀ a b : ℝ, a ≤ 1 → 0 ≤ b → b ≤ 1 →
          0 < scoreWindowGap
            (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))
            (upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)) a b →
          Cη * ((n : ℝ)^3)⁻¹ ≤ scoreWindowGap
            (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))
            (upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)) a b / 4 →
          Cε * ((n : ℝ)^3)⁻¹ ≤ 1 →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
            FixedScoreAchievable setting hs ν r lam (radialSecondCoefficientSup d r lam)
              a b δ (spherePureVector ψ)

/-- Transport the actual full-control event to canonical sphere targets while
retaining the inverse-cube constants in the finite-size protocol consumer. -/
theorem fixedScore_quantitative_from_event (hd : 2 ≤ d)
    (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν]
    (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0 = 1)
    (C₁ C₂ CM Cbad : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hCM : 0 < CM)
    (hbad : 0 ≤ Cbad)
    (hEvent : ∀ᶠ n : ℕ in atTop,
      ∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)), MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad ≤ ENNReal.ofReal (Cbad * ((n : ℝ)^8)⁻¹) ∧
        ∀ U, U ∉ bad → radialReadoutFullControl d n r (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1, p.2)) lam localWeylFin 0 C₁ C₂ CM
          (WithLp.toLp 2 (haarPureVector ψ₀ U).amp)) :
    QuantitativeFixedScoreConclusion setting hs ν r lam := by
  obtain ⟨good, hcompact, hN⟩ :=
    full_control_canonical_targets hd setting ν r lam C₁ C₂ CM Cbad hbad hEvent
  obtain ⟨hE, he⟩ := radialSecondCoefficientSup_bounds d r (by omega) lam h0
  obtain ⟨N, hN⟩ := eventually_atTop.mp hN
  have hη : 0 < completeMeanConstant d r lam C₁ := by
    unfold completeMeanConstant
    exact add_pos_of_pos_of_nonneg hC₁ (by positivity)
  refine ⟨completeMeanConstant d r lam C₁, C₂ + CM, hη, by linarith,
    good, hcompact, max N 1, le_max_right _ _, ?_⟩
  intro n hn
  have hnN := hN n ((le_max_left _ _).trans hn)
  refine ⟨hnN.1, ?_⟩
  intro ψ hψ
  have hcontrol := hnN.2 ψ hψ
  refine ⟨completeReadoutLoewner_of_full_control d n r (by omega) _ _
    ((hs.comp continuous_fst).prodMk continuous_snd) lam h0 _ hE.le
    (fun w => (le_abs_self _).trans (he w)) C₁ C₂ CM (spherePureVector ψ) hcontrol, ?_⟩
  intro a b ha hb0 hb1 hg hmean hsecond δ hδ hhalf
  have ht : 0 ≤ ((n : ℝ)^3)⁻¹ := by positivity
  have hL : (C₁ + 2 * |1 - lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)|) *
      ((n : ℝ)^3)⁻¹ ≤ completeMeanConstant d r lam C₁ * ((n : ℝ)^3)⁻¹ := by
    unfold completeMeanConstant
    nlinarith [mul_nonneg
      (abs_nonneg (1 - upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))) ht]
  have hU : (C₁ + 2 * |1 - upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)|) *
      ((n : ℝ)^3)⁻¹ ≤ completeMeanConstant d r lam C₁ * ((n : ℝ)^3)⁻¹ := by
    unfold completeMeanConstant
    nlinarith [mul_nonneg
      (abs_nonneg (1 - lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))) ht]
  exact fixedScore_achievable_of_full_control hd setting hs ν r lam h0 C₁ C₂ CM
    (radialSecondCoefficientSup d r lam) a b hE.le
    (fun w => (le_abs_self _).trans (he w)) ha hb0 hb1 hg
    (hL.trans hmean) (hU.trans hmean) hsecond (spherePureVector ψ) hcontrol δ hδ hhalf

/-- Haar local bases supply the quantitative target family and finite-size
protocols for every fixed signed score in each dimension d >= 3. -/
theorem fixedScore_haar_quantitative (d r : ℕ) (hd : 3 ≤ d) [NeZero d]
    (lam : ℕ → ℝ) (h0 : lam 0 = 1) :
    QuantitativeFixedScoreConclusion (id : LocalUnitary d → LocalUnitary d) continuous_id
      (complexUnitaryHaar (Fin d)) r lam := by
  obtain ⟨C₁, C₂, CM, hC₁, hC₂, hCM, hEvent⟩ :=
    radialHaar_full_readout_haar_eventually d r hd lam
      (0 : ZMod d × ZMod d) localWeylLabel_card
  let Cbad := radialHighGaussianConstant d r lam +
    2 * radialHighGaussianConstant d r (fun j => (lam j)^2) + 3
  have hbad : 0 ≤ Cbad := by
    have ha := radialHighGaussianConstant_pos d r (by omega) lam
    have hb := radialHighGaussianConstant_pos d r (by omega) (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  apply fixedScore_quantitative_from_event (by omega : 2 ≤ d) id continuous_id
    (complexUnitaryHaar (Fin d)) r lam h0 C₁ C₂ CM Cbad hC₁ hC₂ hCM hbad
  filter_upwards [hEvent] with n hn
  intro ψ₀
  obtain ⟨hm, hp, hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  exact ⟨{U | complexUnitarySphereAction (QuditIndex d n) U ψ₀ ∈
    radialReadoutFullBad d n r (haarBasisRecords d) id lam localWeylFin 0 CM}, hm, hp, hc⟩

/-- Uniform local Pauli bases give the same quantitative statement at d = 2,
with no supplied concentration or protocol-existence premise. -/
theorem fixedScore_pauli_quantitative (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0 = 1) :
    QuantitativeFixedScoreConclusion pauliBasisUnitary continuous_of_discreteTopology
      (uniformFiniteOutcome 3) r lam := by
  obtain ⟨C₁, C₂, CM, hC₁, hC₂, hCM, hEvent⟩ :=
    radialPauli_full_readout_haar_eventually r lam
      (0 : ZMod 2 × ZMod 2) localWeylLabel_card
  let Cbad := radialHighGaussianConstant 2 r lam +
    2 * radialHighGaussianConstant 2 r (fun j => (lam j)^2) + 3
  have hbad : 0 ≤ Cbad := by
    have ha := radialHighGaussianConstant_pos 2 r (by omega) lam
    have hb := radialHighGaussianConstant_pos 2 r (by omega) (fun j => (lam j)^2)
    dsimp only [Cbad]
    linarith
  apply fixedScore_quantitative_from_event (by norm_num : 2 ≤ (2 : ℕ)) pauliBasisUnitary
    continuous_of_discreteTopology (uniformFiniteOutcome 3) r lam h0
    C₁ C₂ CM Cbad hC₁ hC₂ hCM hbad
  filter_upwards [hEvent] with n hn
  intro ψ₀
  obtain ⟨hm, hp, hc⟩ := hn localWeylFin localWeylFin_zero localWeylFin_unitary
    localWeylFin_hilbertSchmidt ψ₀
  exact ⟨{U | complexUnitarySphereAction (QuditIndex 2 n) U ψ₀ ∈
    radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam localWeylFin 0 CM}, hm, hp, hc⟩

/-- One cutoff covers every fidelity window whose score gap is at least K/n.
The conclusion concerns actual protocols and retains their exact finite cap. -/
def UniformScoreGapConclusion (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ) (K : ℝ) : Prop :=
  ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
    (∀ n, IsCompact (good n)) ∧
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ ≤
        ENNReal.ofReal (((n : ℝ)^2)⁻¹) ∧
      ∀ ψ ∈ good n, ∀ a b : ℝ, a ≤ 1 → 0 ≤ b → b ≤ 1 →
        K / (n : ℝ) ≤ scoreWindowGap
          (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))
          (upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)) a b →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
          FixedScoreAchievable setting hs ν r lam (radialSecondCoefficientSup d r lam)
            a b δ (spherePureVector ψ)

private theorem inverse_cube_le_inverse_linear_eventually (C K : ℝ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ)^3)⁻¹ ≤ (K / (n : ℝ)) / 4 := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).pow 2
  have hlimit : Tendsto (fun n : ℕ => 4 * C * ((n : ℝ)^2)⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_apply, inv_pow, zero_pow (by omega : 2 ≠ 0), mul_zero] using
      tendsto_const_nhds.mul hi
  filter_upwards [hlimit.eventually (gt_mem_nhds hK), eventually_ge_atTop 1] with n hbound hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  apply (le_div_iff₀ hnR).mpr
  calc
    C * ((n : ℝ)^3)⁻¹ * 4 * (n : ℝ) = 4 * C * ((n : ℝ)^2)⁻¹ := by
      field_simp
    _ ≤ K := hbound.le

omit [CompactSpace H] in
/-- Inverse-cube control gives one size cutoff for all inverse-linear score
gaps. No fidelity window is fixed before choosing this cutoff. -/
theorem QuantitativeFixedScoreConclusion.uniform_gap
    (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (r : ℕ) (lam : ℕ → ℝ)
    (h : QuantitativeFixedScoreConclusion setting hs ν r lam) (K : ℝ) (hK : 0 < K) :
    UniformScoreGapConclusion setting hs ν r lam K := by
  obtain ⟨Cη, Cε, _hη, _hε, good, hcompact, N, hNpos, hN⟩ := h
  obtain ⟨N', hN'⟩ := eventually_atTop.mp
    ((inverse_cube_le_inverse_linear_eventually Cη K hK).and
      (eventually_inverse_cube_error Cε 1 (by norm_num)))
  refine ⟨good, hcompact, max N N', hNpos.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hnN := (le_max_left _ _).trans hn
  have hnN' := hN' n ((le_max_right _ _).trans hn)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  refine ⟨(hN n hnN).1, ?_⟩
  intro ψ hψ a b ha hb0 hb1 hgap δ hδ hhalf
  have hg : 0 < scoreWindowGap
      (lowerEnvelope ((d : ℝ)+1) (radialPolynomial d r lam))
      (upperEnvelope ((d : ℝ)+1) (radialPolynomial d r lam)) a b :=
    (div_pos hK hnR).trans_le hgap
  exact ((hN n hnN).2 ψ hψ).2 a b ha hb0 hb1 hg
    (hnN'.1.trans (div_le_div_of_nonneg_right hgap (by norm_num))) hnN'.2 δ hδ hhalf

/-- Actual Haar readout admits a common size cutoff for all windows with
score gap at least K/n, for each fixed K > 0. -/
theorem fixedScore_haar_uniform_gap (d r : ℕ) (hd : 3 ≤ d) [NeZero d]
    (lam : ℕ → ℝ) (h0 : lam 0 = 1) (K : ℝ) (hK : 0 < K) :
    UniformScoreGapConclusion (id : LocalUnitary d → LocalUnitary d) continuous_id
      (complexUnitaryHaar (Fin d)) r lam K :=
  (fixedScore_haar_quantitative d r hd lam h0).uniform_gap _ _ _ _ _ K hK

/-- The same common-cutoff moving-window statement for actual Pauli readout. -/
theorem fixedScore_pauli_uniform_gap (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0 = 1)
    (K : ℝ) (hK : 0 < K) :
    UniformScoreGapConclusion pauliBasisUnitary continuous_of_discreteTopology
      (uniformFiniteOutcome 3) r lam K :=
  (fixedScore_pauli_quantitative r lam h0).uniform_gap _ _ _ _ _ K hK

end LocalCertification.Protocol
