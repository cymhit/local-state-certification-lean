import CertificationGaussian.ReadoutMomentContinuity

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- One actual sphere bad set for the original high/low control and the genuine full-second error. -/
def radialReadoutFullBad {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (C : ℝ) :
    Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
  (radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0) ∪
    {ψ | C*((n:ℝ)^3)⁻¹<cardinalityReadoutSecondError d n r μ record lam ψ}

/-- This actual full bad set is Borel; no measurability of a chosen inverse square root is needed. -/
theorem radialReadoutFullBad_measurable {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (d n r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (lam : ℕ → ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (C : ℝ) :
    MeasurableSet (radialReadoutFullBad d n r μ record lam W k0 C) :=
  ((radialHighSphereBad_measurable d n r lam W k0).union
    (radialLowSphereBad_measurable d n r W k0)).union
      ((isOpen_lt continuous_const
        ((cardinalityReadoutSecondError_continuous d n r μ record hr lam).comp continuous_subtype_val)).measurableSet)

/-- The actual complete full-Haar readout error has a canonical-sphere probability bound on one joint event. -/
theorem radialHaar_full_second_canonicalSphere_tail (d r : ℕ) (hd : 3≤d) [NeZero d]
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        (radialReadoutFullBad d n r (haarBasisRecords d) id lam W k0 C)≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+3)*((n:ℝ)^8)⁻¹) := by
  obtain ⟨C,hC,hE⟩ := radialHaar_full_second_control_eventually d r (by omega) lam k0 hcard
  have hc₁ := (radialHighGaussianConstant_pos d r (by omega) lam).le
  have hc₂ := (radialHighGaussianConstant_pos d r (by omega) (fun j => (lam j)^2)).le
  refine ⟨C,hC,?_⟩
  filter_upwards [hE,radialHighLow_canonicalSphere_joint_tail d r (by omega) lam k0 hcard,
    cardinalityHaar_remainder_radius_inverse_power d r 8 hd lam] with n he hl hz
  intro W h0 hW hHS
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨z,hz₀⟩ := (NormedSpace.sphere_nonempty (E:=EuclideanSpace ℂ (QuditIndex d n))).mpr
    (show (0:ℝ)≤1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 := ⟨z,hz₀⟩
  let f := fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)
  let L := radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0
  let E : Set (Fin 2 × QuditIndex d n → ℝ) := {x |
    ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖ ∨
    ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|}
  have hm : Measurable f :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous _).measurable
  have hL := hl W h0 hW hHS
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀,
    Measure.map_apply hm ((radialHighSphereBad_measurable d n r lam W k0).union
      (radialLowSphereBad_measurable d n r W k0))] at hL
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀,
    Measure.map_apply hm (radialReadoutFullBad_measurable d n r (haarBasisRecords d) id continuous_id lam W k0 C)]
  have hsub : f ⁻¹' radialReadoutFullBad d n r (haarBasisRecords d) id lam W k0 C ⊆ (f ⁻¹' L)∪E := by
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
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add hL hz).trans_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The actual complete finite-Pauli readout error has a canonical-sphere probability bound on one joint event. -/
theorem radialPauli_full_second_canonicalSphere_tail (r : ℕ)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=4) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin 2) (Fin 2) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex 2 n))
        (radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam W k0 C)≤
        ENNReal.ofReal ((radialHighGaussianConstant 2 r lam+
          2*radialHighGaussianConstant 2 r (fun j => (lam j)^2)+3)*((n:ℝ)^8)⁻¹) := by
  obtain ⟨C,hC,hE⟩ := radialPauli_full_second_control_eventually r lam k0 hcard
  have hc₁ := (radialHighGaussianConstant_pos 2 r (by omega) lam).le
  have hc₂ := (radialHighGaussianConstant_pos 2 r (by omega) (fun j => (lam j)^2)).le
  refine ⟨C,hC,?_⟩
  filter_upwards [hE,radialHighLow_canonicalSphere_joint_tail 2 r (by omega) lam k0 (by simpa using hcard),
    cardinalityPauli_remainder_radius_inverse_power r 8 lam] with n he hl hz
  intro W h0 hW hHS
  let : Nonempty (QuditIndex 2 n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨z,hz₀⟩ := (NormedSpace.sphere_nonempty (E:=EuclideanSpace ℂ (QuditIndex 2 n))).mpr
    (show (0:ℝ)≤1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1 := ⟨z,hz₀⟩
  let f := fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex 2 n) x)
  let L := radialHighSphereBad 2 n r lam W k0 ∪ radialLowSphereBad 2 n r W k0
  let E : Set (Fin 2 × QuditIndex 2 n → ℝ) := {x |
    ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖ ∨
    ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex 2 n) x-1|}
  have hm : Measurable f :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous _).measurable
  have hL := hl W h0 hW hHS
  rw [← complexGaussian_direction_map (QuditIndex 2 n) e₀,
    Measure.map_apply hm ((radialHighSphereBad_measurable 2 n r lam W k0).union
      (radialLowSphereBad_measurable 2 n r W k0))] at hL
  rw [← complexGaussian_direction_map (QuditIndex 2 n) e₀,
    Measure.map_apply hm (radialReadoutFullBad_measurable 2 n r pauliBasisRecords pauliFullRecord continuous_of_discreteTopology lam W k0 C)]
  have hsub : f ⁻¹' radialReadoutFullBad 2 n r pauliBasisRecords pauliFullRecord lam W k0 C ⊆ (f ⁻¹' L)∪E := by
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
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add hL hz).trans_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end CertificationGaussian
