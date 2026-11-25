import CertificationGaussian.SphereTransport
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace CertificationGaussian
variable (I : Type*) [Fintype I] [Nonempty I]

/-- Genuine polar integration for a positively homogeneous real function.
No radial independence is postulated: this uses the proved density/polar product law. -/
theorem gaussian_homogeneous_polar_integral (k : Nat) (f : EuclideanSpace ℝ I → ℝ)
    (hf : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = r^k*f x) :
    ∫ x, f x ∂stdGaussian (EuclideanSpace ℝ I) =
      (∫ ψ : sphere (0 : EuclideanSpace ℝ I) 1, f ψ ∂sphereArea I) *
        ∫ r : Ioi (0:ℝ), (r:ℝ)^k ∂gaussianRadialMeasure I := by
  let : IsFiniteMeasure (sphereArea I) := ⟨lt_top_iff_ne_top.mpr (sphereArea_mass_ne_top I)⟩
  let E := EuclideanSpace ℝ I
  let μ := stdGaussian E
  let H := homeomorphUnitSphereProd E
  have hr : μ.restrict ({0}ᶜ : Set E) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using stdGaussian_zero_null I
  calc
    _ = ∫ x : ({0}ᶜ : Set E), f x ∂μ.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl, hr]
    _ = ∫ y : sphere (0:E) 1 × Ioi (0:ℝ), f (H.symm y)
        ∂(μ.comap (Subtype.val : ({0}ᶜ : Set E) → E)).map H := by
      rw [H.measurableEmbedding.integral_map]
      simp only [Homeomorph.symm_apply_apply]
    _ = ∫ y : sphere (0:E) 1 × Ioi (0:ℝ), f y.1*(y.2:ℝ)^k
        ∂(sphereArea I).prod (gaussianRadialMeasure I) := by
      rw [stdGaussian_polar_map]
      congr 1
      funext y
      change f ((y.2:ℝ) • (y.1:E)) = _
      rw [hf y.2 y.2.property, mul_comm]
    _ = _ := integral_prod_mul (L := ℝ)
      (fun ψ : sphere (0:E) 1 => f ψ) (fun r : Ioi (0:ℝ) => (r:ℝ)^k)

/-- Gaussian homogeneous expectations factor into an actual radial moment and
an expectation under the independently defined canonical standard sphere probability. -/
theorem gaussian_homogeneous_integral (k : Nat) (f : EuclideanSpace ℝ I → ℝ)
    (hf : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = r^k*f x) :
    ∫ x, f x ∂stdGaussian (EuclideanSpace ℝ I) =
      (∫ x, ‖x‖^k ∂stdGaussian (EuclideanSpace ℝ I)) *
        ∫ ψ : sphere (0 : EuclideanSpace ℝ I) 1, f ψ ∂standardSphereMeasure I := by
  have hn : ∀ (r : ℝ), 0 < r → ∀ x : EuclideanSpace ℝ I,
      ‖r • x‖^k = r^k*‖x‖^k := by
    intro r hr x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  rw [gaussian_homogeneous_polar_integral I k f hf,
    gaussian_homogeneous_polar_integral I k (fun x => ‖x‖^k) hn]
  have hs (ψ : sphere (0 : EuclideanSpace ℝ I) 1) : ‖(ψ : EuclideanSpace ℝ I)‖^k = 1 := by
    rw [mem_sphere_zero_iff_norm.mp ψ.property, one_pow]
  simp_rw [hs]
  rw [standardSphereMeasure, integral_smul_measure]
  simp only [integral_const, smul_eq_mul, mul_one, ENNReal.toReal_inv]
  have hM : (sphereArea I univ).toReal ≠ 0 :=
    (ENNReal.toReal_pos (sphereArea_mass_ne_zero I) (sphereArea_mass_ne_top I)).ne'
  change _ = (((sphereArea I) univ).toReal * _) * (((sphereArea I) univ).toReal⁻¹ * _)
  field_simp

end CertificationGaussian
