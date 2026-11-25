import CertificationGaussian.MeasurableFrameContinuity
import CertificationGaussian.SphereTransfer
import CertificationGaussian.HaarOrbit

/-! # One-sample radial and operator-net transfer

The finite net and the single radius event control an arbitrary family of
operators. The sphere event quantifies over the whole family before a state is
sampled. Its measurability follows from closedness, including uncountable
families. The canonical sphere and full-unitary Haar laws are the actual maps
of the same Gaussian sample, not additional distributional assumptions.
-/

noncomputable section
open MeasureTheory Metric
namespace CertificationGaussian

/-- Discarding the nonnegative constant component introduces no additive
radial error, even when the variance scale is very small or zero. -/
theorem frame_energy_of_good_radius {n t q v : ℝ} (hn : 2 ≤ n) (hv : 0 ≤ v)
    (hq : |q-v| ≤ v/n) (ht : |t-1| ≤ (n^2)⁻¹) :
    (q-(t-1)^2)/t^2 ≤ (1+5/n)*v := by
  obtain ⟨ht0, hinv⟩ := radial_good_inverse hn ht
  have hn0 : 0 < n := by linarith
  let w := 1/n
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw : w ≤ 1/2 := by dsimp [w]; apply (div_le_iff₀ hn0).mpr; linarith
  have hw2 : w^2 ≤ w/2 := by nlinarith
  have hw3 : w^3 ≤ w/4 := by
    have h := mul_le_mul_of_nonneg_left hw2 hw0
    nlinarith
  have hpoly : (1+w)^3 ≤ 1+5*w := by nlinarith
  have hq' : q ≤ v*(1+1/n) := by
    have h := (le_abs_self (q-v)).trans hq
    calc
      q ≤ v/n+v := by linarith
      _ = _ := by ring
  calc
    _ ≤ q/t^2 := div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (sq_nonneg _)
    _ ≤ (v*(1+1/n))/t^2 := div_le_div_of_nonneg_right hq' (sq_nonneg _)
    _ = v*(1+1/n)*(1/t)^2 := by ring
    _ ≤ v*(1+1/n)*(1+1/n)^2 := by gcongr
    _ = v*(1+w)^3 := by dsimp [w]; ring
    _ ≤ v*(1+5*w) := mul_le_mul_of_nonneg_left hpoly hv
    _ = _ := by dsimp [w]; ring

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem gaussianFrameSphereScore_of_good_radius
    (T : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I))
    (hT : ∀ A B, inner ℝ A (T B) = inner ℝ (T A) B)
    (hI : T (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      (Fintype.card I:ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix I I ℂ))
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : Fin 2 × I → ℝ)
    {n v : ℝ} (hn : 2 ≤ n) (hv : 0 ≤ v)
    (hq : |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
      (T (matrixHilbertSchmidt (gaussianCenteredProjector x)))-v| ≤ v/n)
    (ht : |gaussianRadius I x-1| ≤ (n^2)⁻¹) :
    gaussianFrameSphereScore T (sphereDirection e₀ (complexGaussianLift I x)) ≤ (1+5/n)*v := by
  have ht0 := (radial_good_inverse hn ht).1
  have hx : complexGaussianLift I x ≠ 0 := by
    intro hz
    rw [gaussianRadius_eq_norm_sq, hz] at ht0
    norm_num at ht0
  rw [gaussianFrame_radial_identity T hT hI e₀ x hx]
  exact frame_energy_of_good_radius hn hv hq ht

/-- A finite operator net controls every operator in the fixed family on the
one common Gaussian/radius event. No positivity of arbitrary operators is used. -/
theorem gaussianFrameSphereScore_of_net_good
    (𝒯 : Set (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)))
    (S : Finset (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)))
    (hS : ∀ W ∈ S, ∀ A B, inner ℝ A (W B) = inner ℝ (W A) B)
    (hI : ∀ W ∈ S, W (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      (Fintype.card I:ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix I I ℂ))
    {n v : ℝ} (hn : 2 ≤ n) (hv : 0 ≤ v)
    (hcover : ∀ T ∈ 𝒯, ∃ W ∈ S, (Fintype.card I:ℝ)^2 * ‖T-W‖ ≤ v/n)
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : Fin 2 × I → ℝ)
    (hgood : ∀ W ∈ S, |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
      (W (matrixHilbertSchmidt (gaussianCenteredProjector x)))-v| ≤ v/n)
    (hrad : |gaussianRadius I x-1| ≤ (n^2)⁻¹) :
    ∀ T ∈ 𝒯, gaussianFrameSphereScore T (sphereDirection e₀ (complexGaussianLift I x)) ≤
      (1+6/n)*v := by
  intro T hT
  obtain ⟨W, hW, hdist⟩ := hcover T hT
  have hWscore := gaussianFrameSphereScore_of_good_radius W (hS W hW) (hI W hW)
    e₀ x hn hv (hgood W hW) hrad
  have hd := (gaussianFrameSphereScore_dist_le T W
    (sphereDirection e₀ (complexGaussianLift I x))).trans hdist
  have h := (le_abs_self (gaussianFrameSphereScore T (sphereDirection e₀ (complexGaussianLift I x)) -
    gaussianFrameSphereScore W (sphereDirection e₀ (complexGaussianLift I x)))).trans hd
  calc
    _ ≤ v/n + gaussianFrameSphereScore W (sphereDirection e₀ (complexGaussianLift I x)) :=
      (sub_le_iff_le_add).mp h
    _ ≤ v/n+(1+5/n)*v := add_le_add le_rfl hWscore
    _ = _ := by ring

/-- Actual canonical sphere failure is contained in the union of the finite
Gaussian failures and the single radial failure. The Gaussian origin is already
excluded by the good radius event, so no null-set exception is needed. -/
theorem gaussianFrame_common_sphere_failure_le
    (𝒯 : Set (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)))
    (S : Finset (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)))
    (hS : ∀ W ∈ S, ∀ A B, inner ℝ A (W B) = inner ℝ (W A) B)
    (hI : ∀ W ∈ S, W (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      (Fintype.card I:ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix I I ℂ))
    {n v : ℝ} (hn : 2 ≤ n) (hv : 0 ≤ v)
    (hcover : ∀ T ∈ 𝒯, ∃ W ∈ S, (Fintype.card I:ℝ)^2 * ‖T-W‖ ≤ v/n) :
    canonicalSphereMeasure (EuclideanSpace ℂ I)
      {ψ : sphere (0 : EuclideanSpace ℂ I) 1 | ∀ T ∈ 𝒯,
        gaussianFrameSphereScore T ψ ≤ (1+6/n)*v}ᶜ ≤
      (pairedGaussian I)
        ({x | ∃ W ∈ S, v/n ≤ |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
          (W (matrixHilbertSchmidt (gaussianCenteredProjector x)))-v|} ∪
        {x | (n^2)⁻¹ ≤ |gaussianRadius I x-1|}) := by
  obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℂ I)).mpr
    (show (0:ℝ) ≤ 1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ I) 1 := ⟨z,hz⟩
  have hm : Measurable (fun x : Fin 2 × I → ℝ => sphereDirection e₀ (complexGaussianLift I x)) :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous I).measurable
  rw [← complexGaussian_direction_map I e₀,
    Measure.map_apply hm (measurableSet_gaussianFrameSphereScore_uniform_sublevel 𝒯 ((1+6/n)*v)).compl]
  apply measure_mono
  intro x hx
  by_contra hnot
  have hb := not_or.mp hnot
  have hgood : ∀ W ∈ S, |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
      (W (matrixHilbertSchmidt (gaussianCenteredProjector x)))-v| ≤ v/n := by
    intro W hW
    exact (lt_of_not_ge (fun h => hb.1 ⟨W,hW,h⟩)).le
  have hrad : |gaussianRadius I x-1| ≤ (n^2)⁻¹ := (lt_of_not_ge hb.2).le
  exact hx (gaussianFrameSphereScore_of_net_good 𝒯 S hS hI hn hv hcover e₀ x hgood hrad)

/-- The common-event probability is identical under the genuine full-unitary
Haar orbit of every fixed initial unit vector. -/
theorem gaussianFrame_common_haar_failure_eq
    (𝒯 : Set (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)))
    (c : ℝ) (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    complexUnitaryHaar I
      {U | ¬ ∀ T ∈ 𝒯, gaussianFrameSphereScore T (complexUnitarySphereAction I U ψ) ≤ c} =
      canonicalSphereMeasure (EuclideanSpace ℂ I)
        {φ : sphere (0 : EuclideanSpace ℂ I) 1 | ∀ T ∈ 𝒯, gaussianFrameSphereScore T φ ≤ c}ᶜ := by
  have he := congrArg
    (fun μ : Measure (sphere (0 : EuclideanSpace ℂ I) 1) =>
      μ {φ : sphere (0 : EuclideanSpace ℂ I) 1 | ∀ T ∈ 𝒯, gaussianFrameSphereScore T φ ≤ c}ᶜ)
    (complexUnitaryHaar_orbit_map I ψ)
  rw [Measure.map_apply (complexUnitarySphereAction_continuous I).measurable.of_uncurry_right
    (measurableSet_gaussianFrameSphereScore_uniform_sublevel 𝒯 c).compl] at he
  exact he

end CertificationGaussian
