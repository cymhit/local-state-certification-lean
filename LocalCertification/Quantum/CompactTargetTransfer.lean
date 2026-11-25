import LocalCertification.Quantum.HaarProductBasis
import Mathlib.MeasureTheory.Measure.Regular

set_option autoImplicit false
open MeasureTheory Metric Set CertificationGaussian
open scoped ENNReal
noncomputable section
namespace LocalCertification.Quantum

/-- A measurable Haar good event yields a genuine compact set of unit-vector targets. The arbitrary
positive approximation loss may be chosen polynomially or exponentially small. No measurability of
any property subsequently established on the targets is assumed. -/
theorem haar_good_compact_targets (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I]
    (ψ₀ : sphere (0 : EuclideanSpace ℂ I) 1)
    (bad : Set (ComplexUnitary I)) (hm : MeasurableSet bad) (ε : ℝ) (hε : 0<ε) :
    ∃ good : Set (sphere (0 : EuclideanSpace ℂ I) 1),IsCompact good ∧
      canonicalSphereMeasure (EuclideanSpace ℂ I) goodᶜ≤complexUnitaryHaar I bad+ENNReal.ofReal ε ∧
      ∀ ψ∈good,∃ U : ComplexUnitary I,U∉bad ∧ complexUnitarySphereAction I U ψ₀=ψ := by
  let : (complexUnitaryHaar I).Regular := by
    unfold complexUnitaryHaar compactHaarProbability
    infer_instance
  obtain ⟨K,hKgood,hKcompact,hKloss⟩ := hm.compl.exists_isCompact_sdiff_lt
    (measure_ne_top (complexUnitaryHaar I) badᶜ) (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  let f := fun U : ComplexUnitary I => complexUnitarySphereAction I U ψ₀
  have hp : Continuous (fun U : ComplexUnitary I => (U,ψ₀)) :=
    continuous_id.prodMk continuous_const
  have hf : Continuous f := by
    simpa only [f,Function.comp_def,Function.uncurry_apply_pair] using
      (complexUnitarySphereAction_continuous I).comp hp
  have himage := hKcompact.image hf
  refine ⟨f '' K,himage,?_,?_⟩
  · rw [← complexUnitaryHaar_orbit_map I ψ₀,Measure.map_apply hf.measurable himage.isClosed.measurableSet.compl]
    have hpre : f ⁻¹' (f '' K)ᶜ⊆Kᶜ := by
      intro U hU hUK
      exact hU ⟨U,hUK,rfl⟩
    have hcover : Kᶜ⊆bad∪(badᶜ\K) := by
      intro U hU
      by_cases hb : U∈bad
      · exact Or.inl hb
      · exact Or.inr ⟨hb,hU⟩
    calc
      complexUnitaryHaar I (f ⁻¹' (f '' K)ᶜ)≤complexUnitaryHaar I Kᶜ := measure_mono hpre
      _≤complexUnitaryHaar I (bad∪(badᶜ\K)) := measure_mono hcover
      _≤complexUnitaryHaar I bad+complexUnitaryHaar I (badᶜ\K) := measure_union_le _ _
      _≤complexUnitaryHaar I bad+ENNReal.ofReal ε := add_le_add le_rfl hKloss.le
  · intro ψ hψ
    obtain ⟨U,hUK,hUψ⟩ := hψ
    exact ⟨U,hKgood hUK,hUψ⟩

end LocalCertification.Quantum
