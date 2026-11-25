import CertificationGaussian.MeasurableFrameSphereTransfer
import CertificationGaussian.QuarticRadiusSphereTransfer

/-! # Radial transfer for a net of measurement frames

With fourth-power radial precision, the Gaussian estimate and the off-net
error give an explicit finite-size bound for every frame in the covered family.
-/

open CertificationGaussian Metric

namespace LocalCertification.Quantum

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem frame_score_of_quartic_radius
    (T : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I))
    (hsym : ∀ A B, inner ℝ A (T B) = inner ℝ (T A) B)
    (hid : T (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      (Fintype.card I : ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix I I ℂ))
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : Fin 2 × I → ℝ)
    {n v : ℝ} (hn : 2 ≤ n) (hv : 0 ≤ v)
    (hcenter : |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
      (T (matrixHilbertSchmidt (gaussianCenteredProjector x))) - v| ≤ v / n)
    (hrad : |gaussianRadius I x - 1| ≤ (n ^ 4)⁻¹) :
    gaussianFrameSphereScore T (sphereDirection e₀ (complexGaussianLift I x)) ≤
      (1 + 1/n) / (1 - (n ^ 4)⁻¹) ^ 2 * v := by
  have hn0 : 0 < n := by linarith
  have hden := quarticRadius_denominator_pos hn
  have hradlo : 1 - (n ^ 4)⁻¹ ≤ gaussianRadius I x := by
    linarith [(abs_le.mp hrad).1]
  have hx : complexGaussianLift I x ≠ 0 := by
    intro hz
    have ht := hden.trans_le hradlo
    rw [gaussianRadius_eq_norm_sq, hz] at ht
    norm_num at ht
  rw [gaussianFrame_radial_identity T hsym hid e₀ x hx]
  have hnorm := (le_abs_self _).trans hcenter
  calc
    _ ≤ (v + v/n) / (gaussianRadius I x) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith [sq_nonneg (gaussianRadius I x - 1)]
    _ ≤ (v + v/n) / (1 - (n ^ 4)⁻¹) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ hden.le hradlo 2
    _ = _ := by ring

/-- An operator net with scaled error at most `v/n` transfers the bound
to the whole family on the same Gaussian sample. -/
theorem frame_family_score_of_quartic_radius
    (𝒯 : Set (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)))
    (S : Finset (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)))
    (hsym : ∀ W ∈ S, ∀ A B, inner ℝ A (W B) = inner ℝ (W A) B)
    (hid : ∀ W ∈ S, W (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      (Fintype.card I : ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix I I ℂ))
    {n v : ℝ} (hn : 2 ≤ n) (hv : 0 ≤ v)
    (hcover : ∀ T ∈ 𝒯, ∃ W ∈ S, (Fintype.card I : ℝ) ^ 2 * ‖T - W‖ ≤ v/n)
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : Fin 2 × I → ℝ)
    (hcenters : ∀ W ∈ S, |inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
      (W (matrixHilbertSchmidt (gaussianCenteredProjector x))) - v| ≤ v/n)
    (hrad : |gaussianRadius I x - 1| ≤ (n ^ 4)⁻¹) :
    ∀ T ∈ 𝒯, gaussianFrameSphereScore T (sphereDirection e₀ (complexGaussianLift I x)) ≤
      ((1 + 1/n) / (1 - (n ^ 4)⁻¹) ^ 2 + 1/n) * v := by
  intro T hT
  obtain ⟨W, hW, hmesh⟩ := hcover T hT
  have hdist := (gaussianFrameSphereScore_dist_le T W
    (sphereDirection e₀ (complexGaussianLift I x))).trans hmesh
  have h := (le_abs_self _).trans hdist
  have hw := frame_score_of_quartic_radius W (hsym W hW) (hid W hW)
    e₀ x hn hv (hcenters W hW) hrad
  calc
    _ ≤ v/n + gaussianFrameSphereScore W (sphereDirection e₀ (complexGaussianLift I x)) :=
      (sub_le_iff_le_add).mp h
    _ ≤ v/n + (1 + 1/n) / (1 - (n ^ 4)⁻¹) ^ 2 * v := add_le_add le_rfl hw
    _ = _ := by ring

end LocalCertification.Quantum
