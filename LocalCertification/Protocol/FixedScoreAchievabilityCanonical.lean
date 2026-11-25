import LocalCertification.Protocol.FixedScoreAchievability
import LocalCertification.Quantum.CompactTargetTransfer

set_option autoImplicit false
open Matrix MeasureTheory Metric Filter Set CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {H : Type u} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]
  [CompactSpace H] [SecondCountableTopology H] {d : ℕ} [NeZero d]

omit [TopologicalSpace H] [BorelSpace H] [CompactSpace H] [SecondCountableTopology H] in
/-- One compact canonical target sequence retains the entire actual operator control. The
inner-regular approximation costs only n^-8, so the total complement is eventually at most n^-2. -/
theorem full_control_canonical_targets (hd : 2≤d)
    (setting : H → LocalUnitary d) (ν : Measure H) (r : ℕ) (lam : ℕ → ℝ)
    (C₁ C₂ CM Cbad : ℝ) (hbad : 0≤Cbad)
    (hEvent : ∀ᶠ n : ℕ in atTop,∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (Cbad*((n:ℝ)^8)⁻¹) ∧
        ∀ U,U∉bad → radialReadoutFullControl d n r (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1,p.2)) lam localWeylFin 0 C₁ C₂ CM
          (WithLp.toLp 2 (haarPureVector ψ₀ U).amp)) :
    ∃ good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1),
      (∀ n,IsCompact (good n)) ∧ ∀ᶠ n : ℕ in atTop,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
      ∀ ψ∈good n,radialReadoutFullControl d n r (ν.prod (uniformFiniteOutcome d))
        (fun p : H × Fin d => (setting p.1,p.2)) lam localWeylFin 0 C₁ C₂ CM
        (WithLp.toLp 2 (spherePureVector ψ).amp) := by
  classical
  let P (n : ℕ) (s : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)) : Prop :=
    IsCompact s ∧ canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) sᶜ≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
      ∀ ψ∈s,radialReadoutFullControl d n r (ν.prod (uniformFiniteOutcome d))
        (fun p : H × Fin d => (setting p.1,p.2)) lam localWeylFin 0 C₁ C₂ CM
        (WithLp.toLp 2 (spherePureVector ψ).amp)
  have hN : ∀ᶠ n : ℕ in atTop,∃ s,P n s := by
    filter_upwards [hEvent,eventually_ge_atTop 1,completeReadout_failure_le_inverse_square (Cbad+1)]
      with n hn hn1 habs
    let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
    obtain ⟨ψ₀⟩ := NormedSpace.sphere_nonempty_rclike (E:=EuclideanSpace ℂ (QuditIndex d n)) ℂ
      (show (0:ℝ)≤1 by norm_num)
    obtain ⟨bad,hm,hp,hc⟩ := hn ψ₀
    have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have ht : 0<((n:ℝ)^8)⁻¹ := by positivity
    obtain ⟨good,hcompact,hprob,hfiber⟩ := haar_good_compact_targets (QuditIndex d n) ψ₀ bad hm
      (((n:ℝ)^8)⁻¹) ht
    refine ⟨good,hcompact,?_,?_⟩
    · calc
        _≤complexUnitaryHaar (QuditIndex d n) bad+ENNReal.ofReal (((n:ℝ)^8)⁻¹) := hprob
        _≤ENNReal.ofReal (Cbad*((n:ℝ)^8)⁻¹)+ENNReal.ofReal (((n:ℝ)^8)⁻¹) := add_le_add hp le_rfl
        _=ENNReal.ofReal ((Cbad+1)*((n:ℝ)^8)⁻¹) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hbad ht.le) ht.le]
          congr 1
          ring
        _≤_ := ENNReal.ofReal_le_ofReal habs
    · intro ψ hψ
      obtain ⟨U,hU,hUψ⟩ := hfiber ψ hψ
      simpa only [haarPureVector,hUψ] using hc U hU
  let good (n : ℕ) : Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
    if h : ∃ s,P n s then h.choose else ∅
  have hcompact (n : ℕ) : IsCompact (good n) := by
    by_cases h : ∃ s,P n s
    · simpa only [good,dite_eq_left h] using h.choose_spec.1
    · simpa only [good,dite_eq_right h] using isCompact_empty
  refine ⟨good,hcompact,?_⟩
  filter_upwards [hN] with n hn
  have h : ∃ s,P n s := hn
  have hP : P n (good n) := by simpa only [good,dite_eq_left h] using h.choose_spec
  exact hP.2

/-- The same canonical target sets give every original Loewner bound and every positive-gap
raw protocol with the exact e_* and 1548 V/Delta² budget. Sets are fixed before a,b and delta. -/
theorem fixedScore_canonical_from_event (hd : 2≤d)
    (setting : H → LocalUnitary d) (hs : Continuous setting) (ν : Measure H) [IsProbabilityMeasure ν]
    (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0=1)
    (C₁ C₂ CM Cbad : ℝ) (hC₁ : 0<C₁) (hC₂ : 0<C₂) (hCM : 0<CM) (hbad : 0≤Cbad)
    (hEvent : ∀ᶠ n : ℕ in atTop,∀ ψ₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∃ bad : Set (ComplexUnitary (QuditIndex d n)),MeasurableSet bad ∧
        complexUnitaryHaar (QuditIndex d n) bad≤ENNReal.ofReal (Cbad*((n:ℝ)^8)⁻¹) ∧
        ∀ U,U∉bad → radialReadoutFullControl d n r (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1,p.2)) lam localWeylFin 0 C₁ C₂ CM
          (WithLp.toLp 2 (haarPureVector ψ₀ U).amp)) :
    ∃ (η ε : ℕ → ℝ) (good : (n : ℕ) → Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)),
      (∀ n,IsCompact (good n)) ∧ (∀ n,0≤η n ∧ 0≤ε n) ∧
      Tendsto η atTop (nhds 0) ∧ Tendsto ε atTop (nhds 0) ∧
      (∀ᶠ n : ℕ in atTop,
        canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (good n)ᶜ≤ENNReal.ofReal (((n:ℝ)^2)⁻¹) ∧
        ∀ ψ∈good n,completeReadoutLoewner d n r (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1,p.2)) lam (radialSecondCoefficientSup d r lam)
          (η n) (ε n) (spherePureVector ψ)) ∧
      ∀ a b : ℝ,a≤1 → 0≤b → b≤1 →
        0<scoreWindowGap (lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
          (upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)) a b →
        ∀ᶠ n : ℕ in atTop,∀ ψ∈good n,∀ δ : ℝ,0<δ → δ≤1/2 →
          FixedScoreAchievable setting hs ν r lam (radialSecondCoefficientSup d r lam) a b δ (spherePureVector ψ) := by
  obtain ⟨good,hcompact,hN⟩ := full_control_canonical_targets hd setting ν r lam C₁ C₂ CM Cbad hbad hEvent
  obtain ⟨hE,he⟩ := radialSecondCoefficientSup_bounds d r (by omega) lam h0
  have hη : 0<completeMeanConstant d r lam C₁ := by
    unfold completeMeanConstant
    exact add_pos_of_pos_of_nonneg hC₁ (by positivity)
  refine ⟨fun n => completeMeanConstant d r lam C₁*((n:ℝ)^3)⁻¹,
    fun n => (C₂+CM)*((n:ℝ)^3)⁻¹,good,hcompact,fun n => ⟨by positivity,by positivity⟩,
    completeReadout_error_tendsto_zero _,completeReadout_error_tendsto_zero _,?_,?_⟩
  · filter_upwards [hN] with n hn
    refine ⟨hn.1,?_⟩
    intro ψ hψ
    exact completeReadoutLoewner_of_full_control d n r (by omega) _ _
      ((hs.comp continuous_fst).prodMk continuous_snd) lam h0 _ hE.le
      (fun w => (le_abs_self _).trans (he w)) C₁ C₂ CM (spherePureVector ψ) (hn.2 ψ hψ)
  · intro a b ha hb0 hb1 hg
    have hRun := fixedScore_achievable_of_full_control_eventually hd setting hs ν r lam h0 C₁ C₂ CM
      (radialSecondCoefficientSup d r lam) a b hE.le (fun w => (le_abs_self _).trans (he w)) ha hb0 hb1 hg
    filter_upwards [hN,hRun] with n hn hr
    intro ψ hψ δ hδ hhalf
    exact hr (spherePureVector ψ) (hn.2 ψ hψ) δ hδ hhalf

end LocalCertification.Protocol
