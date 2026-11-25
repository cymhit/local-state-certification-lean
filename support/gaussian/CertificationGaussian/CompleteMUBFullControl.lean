import CertificationGaussian.CompleteMUBFullSecond

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Actual finite-MUB full-second bad set under the genuine canonical sphere law. -/
theorem radialMUB_full_second_canonicalSphere_tail (d r : ℕ) (hd : 2≤d) [NeZero d] (B : CompleteMUB d)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n))
        (radialReadoutFullBad d n r (completeMUBRecords d) (completeMUBFullRecord B) lam W k0 C)≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+3)*((n:ℝ)^8)⁻¹) := by
  obtain ⟨C,hC,hE⟩ := radialMUB_full_second_control_eventually d r (by omega) B lam k0 hcard
  have hc₁ := (radialHighGaussianConstant_pos d r (by omega) lam).le
  have hc₂ := (radialHighGaussianConstant_pos d r (by omega) (fun j => (lam j)^2)).le
  refine ⟨C,hC,?_⟩
  filter_upwards [hE,radialHighLow_canonicalSphere_joint_tail d r (by omega) lam k0 hcard,
    cardinalityMUB_remainder_radius_inverse_power d r 8 B hd lam] with n he hl hz
  intro W h0 hW hHS
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  obtain ⟨z,hz₀⟩ := (NormedSpace.sphere_nonempty (E:=EuclideanSpace ℂ (QuditIndex d n))).mpr
    (show (0:ℝ)≤1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 := ⟨z,hz₀⟩
  let f := fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)
  let L := radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0
  let E : Set (Fin 2 × QuditIndex d n → ℝ) := {x |
    ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B) r lam (complexCoordinate x))‖ ∨
    ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|}
  have hm : Measurable f :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous _).measurable
  have hL := hl W h0 hW hHS
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀,
    Measure.map_apply hm ((radialHighSphereBad_measurable d n r lam W k0).union
      (radialLowSphereBad_measurable d n r W k0))] at hL
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀,
    Measure.map_apply hm (radialReadoutFullBad_measurable d n r (completeMUBRecords d) (completeMUBFullRecord B) continuous_of_discreteTopology lam W k0 C)]
  have hsub : f ⁻¹' radialReadoutFullBad d n r (completeMUBRecords d) (completeMUBFullRecord B) lam W k0 C ⊆ (f ⁻¹' L)∪E := by
    intro x hx
    by_cases hlow : f x∈L
    · exact Or.inl hlow
    · apply Or.inr
      by_contra hnot
      have hn : ¬(((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
          (cardinalityReadoutRemainder (S:=Fin n) d (completeMUBRecords d) (completeMUBFullRecord B) r lam (complexCoordinate x))‖ ∨
          ((n:ℝ)^(r+4))⁻¹< |gaussianRadius (QuditIndex d n) x-1|) := hnot
      have hbound := he W h0 hHS e₀ x hlow
        (le_of_not_gt (not_or.mp hn).2) (le_of_not_gt (not_or.mp hn).1)
      exact not_lt_of_ge hbound (Or.resolve_left hx hlow)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add hL hz).trans_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- One genuine Haar event controls the original finite-MUB B, S and full M by the same CFC Q.
No design, local moment, contraction, spectral, or B/S norm assumption remains. -/
theorem radialMUB_full_readout_haar_eventually (d r : ℕ) (hd : 2≤d) [NeZero d] (B : CompleteMUB d)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C₁ C₂ CM : ℝ,0<C₁ ∧ 0<C₂ ∧ 0<CM ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      MeasurableSet {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialReadoutFullBad d n r (completeMUBRecords d) (completeMUBFullRecord B) lam W k0 CM} ∧
      complexUnitaryHaar (QuditIndex d n) {U | complexUnitarySphereAction (QuditIndex d n) U ψ∈
        radialReadoutFullBad d n r (completeMUBRecords d) (completeMUBFullRecord B) lam W k0 CM}≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2)+3)*((n:ℝ)^8)⁻¹) ∧
      ∀ U,complexUnitarySphereAction (QuditIndex d n) U ψ∉
        radialReadoutFullBad d n r (completeMUBRecords d) (completeMUBFullRecord B) lam W k0 CM →
        radialReadoutFullControl d n r (completeMUBRecords d) (completeMUBFullRecord B) lam W k0 C₁ C₂ CM
          (complexUnitarySphereAction (QuditIndex d n) U ψ) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hE⟩ := radialMUBReadoutPolar_control_eventually d r (by omega) B lam k0 hcard
  obtain ⟨CM,hCM,hT⟩ := radialMUB_full_second_canonicalSphere_tail d r hd B lam k0 hcard
  refine ⟨C₁,C₂,CM,hC₁,hC₂,hCM,?_⟩
  filter_upwards [hE,hT] with n he ht
  intro W h0 hW hHS ψ
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hm := radialReadoutFullBad_measurable d n r (completeMUBRecords d) (completeMUBFullRecord B) continuous_of_discreteTopology lam W k0 CM
  have hp := ht W h0 hW hHS
  rw [← complexUnitaryHaar_orbit_map (QuditIndex d n) ψ,
    Measure.map_apply (complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm] at hp
  refine ⟨(complexUnitarySphereAction_continuous _).measurable.of_uncurry_right hm,hp,?_⟩
  intro U hg
  apply radialReadoutFullControl_of_bounds d n r (completeMUBRecords d) (completeMUBFullRecord B) lam W k0 C₁ C₂ CM _
  · exact he W h0 hHS _ (fun h => hg (Or.inl h))
  · exact le_of_not_gt (fun h => hg (Or.inr h))

end CertificationGaussian
