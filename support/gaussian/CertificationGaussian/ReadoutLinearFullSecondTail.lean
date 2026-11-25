import CertificationGaussian.ReadoutLinearFullSecondControl
import CertificationGaussian.ReadoutMomentContinuity

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- A common rate for the original high/low events and the actual local-kappa remainder. -/
def radialLinearFullRate (d : ℕ) (ε κ : ℝ) : ℝ :=
  min (radialLinearReadoutRate d ε) (-(Real.log κ/2))

theorem radialLinearFullRate_pos (d : ℕ) (hd : 2≤d) (ε : ℝ) (hε : 0<ε)
    (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2) (κ : ℝ) (hκ : 0<κ) (hκ1 : κ<1) :
    0<radialLinearFullRate d ε κ :=
  lt_min (radialLinearReadoutRate_pos d hd ε hε hgap) (by linarith [Real.log_neg hκ hκ1])

/-- The ratio involving Z and the radius has the same positive exponential rate. -/
theorem radialLinear_remainder_radius_exp_le (d n : ℕ) (hd : 2≤d) (hn : 1≤n) (ε κ : ℝ) :
    Real.exp ((Real.log κ/2)*n)+Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)^3)≤
      2*Real.exp (-radialLinearFullRate d ε κ*n) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hcube : (n:ℝ)≤(n:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1≤3 by omega)
  have hb : 0<Real.log (d:ℝ)/4 := div_pos (Real.log_pos (by exact_mod_cast (show 1<d by omega))) (by norm_num)
  have hc1 : radialLinearFullRate d ε κ≤ -(Real.log κ/2) := min_le_right _ _
  have hc2 : radialLinearFullRate d ε κ≤Real.log (d:ℝ)/4 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have h1 : Real.exp ((Real.log κ/2)*n)≤Real.exp (-radialLinearFullRate d ε κ*n) := by
    simpa only [neg_neg] using radialLinear_exp_rate_le n _ _ hc1
  have h2 : Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)^3)≤Real.exp (-radialLinearFullRate d ε κ*n) := by
    refine (Real.exp_le_exp.mpr (show -(Real.log (d:ℝ)/4)*(n:ℝ)^3≤ -(Real.log (d:ℝ)/4)*n by nlinarith)).trans ?_
    exact radialLinear_exp_rate_le n _ _ hc2
  linarith

/-- One actual sphere bad set for the original high/low control and the genuine full-second error. -/
def radialLinearReadoutFullBad {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (ε : ℝ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (C : ℝ) :
    Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
  (radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0) ∪
    {ψ | C*((n:ℝ)^3)⁻¹<cardinalityReadoutSecondError d n r μ record lam ψ}

/-- This actual full bad set is Borel; no measurability of a chosen inverse square root is needed. -/
theorem radialLinearReadoutFullBad_measurable {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (d n r : ℕ) (ε : ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (C : ℝ) :
    MeasurableSet (radialLinearReadoutFullBad d n r ε μ record lam W k0 C) :=
  ((radialLinearHighSphereBad_measurable d n r ε lam W k0).union
    (radialLinearLowSphereBad_measurable d n ε W k0)).union
      ((isOpen_lt continuous_const
        ((cardinalityReadoutSecondError_continuous d n r μ record hr lam).comp continuous_subtype_val)).measurableSet)

/-- The actual complete full-Haar readout error has a canonical-sphere probability bound on one joint event. -/
theorem radialLinearHaar_full_second_canonicalSphere_tail (d r : ℕ) (hd : 3≤d) [NeZero d]
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        (radialLinearReadoutFullBad d n r ε (haarBasisRecords d) id lam W k0 C)≤
        ENNReal.ofReal (6*Real.exp (-radialLinearFullRate d ε (haarLocalKappa d)*n)) := by
  obtain ⟨C,hC,hE⟩ := radialLinearHaar_full_second_control_eventually d r (by omega) ε hε hhalf hgap lam k0 hcard
  refine ⟨C,hC,?_⟩
  filter_upwards [hE,radialLinearHighLow_canonicalSphere_joint_tail d r (by omega) ε hε hhalf hgap lam k0 hcard,
    cardinalityHaar_remainder_radius_eventually_bound d r hd lam,eventually_ge_atTop 1] with n he hl hz hn1
  intro W h0 hW hHS
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨z,hz₀⟩ := (NormedSpace.sphere_nonempty (E:=EuclideanSpace ℂ (QuditIndex d n))).mpr
    (show (0:ℝ)≤1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 := ⟨z,hz₀⟩
  let f := fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)
  let L := radialLinearHighSphereBad d n r ε lam W k0 ∪ radialLinearLowSphereBad d n ε W k0
  let E : Set (Fin 2 × QuditIndex d n → ℝ) := {x |
    ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖ ∨
    ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|}
  have hm : Measurable f :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous _).measurable
  have hL := hl W h0 hW hHS
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀,
    Measure.map_apply hm ((radialLinearHighSphereBad_measurable d n r ε lam W k0).union
      (radialLinearLowSphereBad_measurable d n ε W k0))] at hL
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀,
    Measure.map_apply hm (radialLinearReadoutFullBad_measurable d n r ε (haarBasisRecords d) id continuous_id lam W k0 C)]
  have hsub : f ⁻¹' radialLinearReadoutFullBad d n r ε (haarBasisRecords d) id lam W k0 C ⊆ (f ⁻¹' L)∪E := by
    intro x hx
    by_cases hlow : f x∈L
    · exact Or.inl hlow
    · apply Or.inr
      by_contra hnot
      have hn : ¬(((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖ ∨
          ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|) := hnot
      have hbound := he W h0 hHS e₀ x hlow
        (le_of_not_gt (not_or.mp hn).2) (le_of_not_gt (not_or.mp hn).1)
      exact not_lt_of_ge hbound (Or.resolve_left hx hlow)
  have hL' : pairedGaussian (QuditIndex d n) (f ⁻¹' L)≤
      ENNReal.ofReal (4*Real.exp (-radialLinearFullRate d ε (haarLocalKappa d)*n)) :=
    hL.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (radialLinear_exp_rate_le n _ _ (min_le_left _ _)) (by norm_num : (0:ℝ)≤4)))
  have hz' : pairedGaussian (QuditIndex d n) E≤
      ENNReal.ofReal (2*Real.exp (-radialLinearFullRate d ε (haarLocalKappa d)*n)) :=
    hz.trans (ENNReal.ofReal_le_ofReal (radialLinear_remainder_radius_exp_le d n (by omega) hn1 ε (haarLocalKappa d)))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add hL' hz').trans_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The actual complete finite-Pauli readout error has a canonical-sphere probability bound on one joint event. -/
theorem radialLinearPauli_full_second_canonicalSphere_tail (r : ℕ) (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2)
    (hgap : radialLinearEntropy 2 ε<Real.log (2:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=4) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin 2) (Fin 2) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 n))
        (radialLinearReadoutFullBad 2 n r ε pauliBasisRecords pauliFullRecord lam W k0 C)≤
        ENNReal.ofReal (6*Real.exp (-radialLinearFullRate 2 ε (pauliLocalKappa)*n)) := by
  obtain ⟨C,hC,hE⟩ := radialLinearPauli_full_second_control_eventually r ε hε hhalf hgap lam k0 hcard
  refine ⟨C,hC,?_⟩
  filter_upwards [hE,radialLinearHighLow_canonicalSphere_joint_tail 2 r (by omega) ε hε hhalf hgap lam k0 (by simpa using hcard),
    cardinalityPauli_remainder_radius_eventually_bound r lam,eventually_ge_atTop 1] with n he hl hz hn1
  intro W h0 hW hHS
  let : Nonempty (QuditIndex 2 n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨z,hz₀⟩ := (NormedSpace.sphere_nonempty (E:=EuclideanSpace ℂ (QuditIndex 2 n))).mpr
    (show (0:ℝ)≤1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1 := ⟨z,hz₀⟩
  let f := fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex 2 n) x)
  let L := radialLinearHighSphereBad 2 n r ε lam W k0 ∪ radialLinearLowSphereBad 2 n ε W k0
  let E : Set (Fin 2 × QuditIndex 2 n → ℝ) := {x |
    ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖ ∨
    ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 2 n) x-1|}
  have hm : Measurable f :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous _).measurable
  have hL := hl W h0 hW hHS
  rw [← complexGaussian_direction_map (QuditIndex 2 n) e₀,
    Measure.map_apply hm ((radialLinearHighSphereBad_measurable 2 n r ε lam W k0).union
      (radialLinearLowSphereBad_measurable 2 n ε W k0))] at hL
  rw [← complexGaussian_direction_map (QuditIndex 2 n) e₀,
    Measure.map_apply hm (radialLinearReadoutFullBad_measurable 2 n r ε pauliBasisRecords pauliFullRecord continuous_of_discreteTopology lam W k0 C)]
  have hsub : f ⁻¹' radialLinearReadoutFullBad 2 n r ε pauliBasisRecords pauliFullRecord lam W k0 C ⊆ (f ⁻¹' L)∪E := by
    intro x hx
    by_cases hlow : f x∈L
    · exact Or.inl hlow
    · apply Or.inr
      by_contra hnot
      have hn : ¬(((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖ ∨
          ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 2 n) x-1|) := hnot
      have hbound := he W h0 hHS e₀ x hlow
        (le_of_not_gt (not_or.mp hn).2) (le_of_not_gt (not_or.mp hn).1)
      exact not_lt_of_ge hbound (Or.resolve_left hx hlow)
  have hL' : pairedGaussian (QuditIndex 2 n) (f ⁻¹' L)≤
      ENNReal.ofReal (4*Real.exp (-radialLinearFullRate 2 ε (pauliLocalKappa)*n)) :=
    hL.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (radialLinear_exp_rate_le n _ _ (min_le_left _ _)) (by norm_num : (0:ℝ)≤4)))
  have hz' : pairedGaussian (QuditIndex 2 n) E≤
      ENNReal.ofReal (2*Real.exp (-radialLinearFullRate 2 ε (pauliLocalKappa)*n)) :=
    hz.trans (ENNReal.ofReal_le_ofReal (radialLinear_remainder_radius_exp_le 2 n (by omega) hn1 ε (pauliLocalKappa)))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add hL' hz').trans_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end CertificationGaussian
