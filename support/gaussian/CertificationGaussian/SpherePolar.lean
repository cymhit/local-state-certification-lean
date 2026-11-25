import CertificationGaussian.GaussianDensity
import Mathlib.MeasureTheory.Constructions.HaarToSphere

noncomputable section
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Classical
namespace CertificationGaussian

/-- Density pullback along an actual measurable embedding. -/
theorem comap_withDensity {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure E) (f : Ω → E) (hf : MeasurableEmbedding f) (ρ : E → ℝ≥0∞) (hρ : Measurable ρ) :
    (μ.withDensity ρ).comap f = (μ.comap f).withDensity (ρ ∘ f) := by
  apply hf.map_injective
  rw [hf.map_comap, map_withDensity_comp _ _ hf.measurable _ hρ,
    hf.map_comap, restrict_withDensity hf.measurableSet_range]

section Direction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual normalization, with an arbitrary unit vector only at the origin. -/
def sphereDirection (e₀ : sphere (0 : E) 1) (x : E) : sphere (0 : E) 1 :=
  if hx : x = 0 then e₀ else
    (homeomorphUnitSphereProd E ⟨x, by simpa using hx⟩).1

theorem sphereDirection_coe (e₀ : sphere (0 : E) 1) (x : E) :
    (sphereDirection e₀ x : E) = if x = 0 then (e₀ : E) else ‖x‖⁻¹ • x := by
  by_cases hx : x = 0 <;> simp [sphereDirection, hx]

theorem sphereDirection_measurable [MeasurableSpace E] [BorelSpace E] (e₀ : sphere (0 : E) 1) : Measurable (sphereDirection e₀) := by
  apply (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).measurable_comp_iff.mp
  change Measurable (fun x => (sphereDirection e₀ x : E))
  simp only [sphereDirection_coe]
  exact Measurable.ite (measurableSet_singleton (0 : E)) measurable_const ((measurable_norm : Measurable (fun x : E => ‖x‖)).inv.smul measurable_id)

theorem sphereDirection_nonzero (e₀ : sphere (0 : E) 1) (x : ({0}ᶜ : Set E)) :
    sphereDirection e₀ x.1 = (homeomorphUnitSphereProd E x).1 := by
  simp [sphereDirection, show x.1 ≠ 0 by simpa only [mem_compl_iff, mem_singleton_iff] using x.2]

end Direction

variable (I : Type*) [Fintype I]

/-- Standard area is defined from canonical volume, independently of every Gaussian. -/
def sphereArea : Measure (sphere (0 : EuclideanSpace ℝ I) 1) :=
  (volume : Measure (EuclideanSpace ℝ I)).toSphere

/-- The normalized standard sphere probability; no Gaussian appears in its definition. -/
def standardSphereMeasure : Measure (sphere (0 : EuclideanSpace ℝ I) 1) :=
  (sphereArea I univ)⁻¹ • sphereArea I

def gaussianRadialMeasure : Measure (Ioi (0 : ℝ)) :=
  (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ I)-1)).withDensity
    (fun r => gaussianRadialDensity (Fintype.card I) r.1)

instance gaussianRadialMeasure_sigmaFinite : SigmaFinite (gaussianRadialMeasure I) := by
  unfold gaussianRadialMeasure gaussianRadialDensity
  infer_instance

/-- The actual Gaussian density transported through the standard volume polar decomposition. -/
theorem stdGaussian_polar_map :
    ((stdGaussian (EuclideanSpace ℝ I)).comap
      (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℝ I)) → EuclideanSpace ℝ I)).map
      (homeomorphUnitSphereProd (EuclideanSpace ℝ I)) =
      (sphereArea I).prod (gaussianRadialMeasure I) := by
  let H := homeomorphUnitSphereProd (EuclideanSpace ℝ I)
  rw [stdGaussian_eq_radial_withDensity, comap_withDensity _ _
    (MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl) _ (by fun_prop)]
  have he : (fun x : ({0}ᶜ : Set (EuclideanSpace ℝ I)) =>
      gaussianRadialDensity (Fintype.card I) ‖(x:EuclideanSpace ℝ I)‖) =
      (fun y : sphere (0 : EuclideanSpace ℝ I) 1 × Ioi (0:ℝ) =>
        gaussianRadialDensity (Fintype.card I) y.2.1) ∘ H := by
    funext x
    simp [H]
  change ((volume.comap (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℝ I)) → _)).withDensity
    (fun x => gaussianRadialDensity (Fintype.card I) ‖(x:EuclideanSpace ℝ I)‖)).map H = _
  rw [he, map_withDensity_comp _ _ H.measurable _ (by fun_prop)]
  rw [(Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace ℝ I))).map_eq]
  exact (prod_withDensity_right
    (μ := sphereArea I)
    (ν := Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ I)-1))
    (g := fun r : Ioi (0:ℝ) => gaussianRadialDensity (Fintype.card I) r.1)
    ((gaussianRadialDensity_measurable (Fintype.card I)).comp measurable_subtype_coe)).symm

theorem sphereArea_mass_ne_top : sphereArea I univ ≠ ∞ := by
  unfold sphereArea
  finiteness

variable [Nonempty I]
theorem sphereArea_mass_ne_zero : sphereArea I univ ≠ 0 := by
  apply Measure.measure_univ_ne_zero.mpr
  exact Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ I))

instance standardSphereMeasure_probability : IsProbabilityMeasure (standardSphereMeasure I) where
  measure_univ := by
    rw [standardSphereMeasure, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (sphereArea_mass_ne_zero I) (sphereArea_mass_ne_top I)

theorem stdGaussian_nonzero_comap_mass :
    ((stdGaussian (EuclideanSpace ℝ I)).comap
      (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℝ I)) → EuclideanSpace ℝ I)) univ = 1 := by
  rw [comap_subtype_coe_apply (measurableSet_singleton _).compl, image_univ, Subtype.range_coe,
    measure_compl (measurableSet_singleton _) (by finiteness), stdGaussian_zero_null]
  simp

/-- Total Gaussian probability identifies the radial factor without evaluating any Gamma integral. -/
theorem gaussianPolar_mass_identity :
    sphereArea I univ * gaussianRadialMeasure I univ = 1 := by
  have h := congrArg (fun μ : Measure (sphere (0 : EuclideanSpace ℝ I) 1 × Ioi (0:ℝ)) => μ univ)
    (stdGaussian_polar_map I)
  rw [Measure.map_apply (homeomorphUnitSphereProd (EuclideanSpace ℝ I)).measurable MeasurableSet.univ,
    preimage_univ, stdGaussian_nonzero_comap_mass] at h
  rw [← univ_prod_univ, Measure.prod_prod] at h
  exact h.symm

theorem gaussianRadialMeasure_mass : gaussianRadialMeasure I univ = (sphereArea I univ)⁻¹ := by
  calc
    _ = (sphereArea I univ)⁻¹ * (sphereArea I univ * gaussianRadialMeasure I univ) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (sphereArea_mass_ne_zero I) (sphereArea_mass_ne_top I), one_mul]
    _ = _ := by rw [gaussianPolar_mass_identity, mul_one]

/-- The angular marginal is the independently defined normalized standard area measure. -/
theorem gaussianPolar_angular_marginal :
    (((stdGaussian (EuclideanSpace ℝ I)).comap
      (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℝ I)) → EuclideanSpace ℝ I)).map
      (homeomorphUnitSphereProd (EuclideanSpace ℝ I))).map Prod.fst = standardSphereMeasure I := by
  rw [stdGaussian_polar_map, Measure.map_fst_prod, gaussianRadialMeasure_mass]
  rfl

/-- Gaussian normalization has the canonical normalized area law, independently of its value at zero. -/
theorem stdGaussian_direction_map (e₀ : sphere (0 : EuclideanSpace ℝ I) 1) :
    (stdGaussian (EuclideanSpace ℝ I)).map (sphereDirection e₀) = standardSphereMeasure I := by
  let E := EuclideanSpace ℝ I
  let μ := stdGaussian E
  have hr : μ.restrict ({0}ᶜ : Set E) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using stdGaussian_zero_null I
  have hm : (μ.comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val = μ := by
    rw [map_comap_subtype_coe (measurableSet_singleton _).compl, hr]
  calc
    μ.map (sphereDirection e₀) =
        ((μ.comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val).map (sphereDirection e₀) := by rw [hm]
    _ = (μ.comap (Subtype.val : ({0}ᶜ : Set E) → E)).map
        (Prod.fst ∘ homeomorphUnitSphereProd E) := by
      rw [Measure.map_map (sphereDirection_measurable e₀) measurable_subtype_coe]
      congr 1
      funext x
      exact sphereDirection_nonzero e₀ x
    _ = _ := by
      rw [← Measure.map_map measurable_fst (homeomorphUnitSphereProd E).measurable]
      exact gaussianPolar_angular_marginal I

end CertificationGaussian
