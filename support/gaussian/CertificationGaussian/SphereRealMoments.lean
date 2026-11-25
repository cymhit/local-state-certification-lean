import CertificationGaussian.SphereHomogeneous
import CertificationGaussian.GaussianWick4

noncomputable section
open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators
namespace CertificationGaussian
variable (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I]

/-- The actual canonical real sphere has covariance identity divided by its dimension. -/
theorem standardSphere_coordinate_second_moment (i j : I) :
    ∫ ψ : sphere (0 : EuclideanSpace ℝ I) 1, ψ.val i*ψ.val j ∂standardSphereMeasure I =
      (if i=j then 1 else 0)/(Fintype.card I : ℝ) := by
  have h := gaussian_homogeneous_integral I 2 (fun x => x i*x j) (by
    intro r _ x
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring)
  rw [stdGaussian_coordinate_second_moment, stdGaussian_norm_second_moment] at h
  apply (eq_div_iff (show (Fintype.card I : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)).mpr
  simpa only [mul_comm] using h.symm

/-- The actual canonical real sphere fourth moment, with radial factor m(m+2). -/
theorem standardSphere_coordinate_fourth_moment (i j k l : I) :
    ∫ ψ : sphere (0 : EuclideanSpace ℝ I) 1,
      ψ.val i*ψ.val j*ψ.val k*ψ.val l ∂standardSphereMeasure I =
      ((if i=j then 1 else 0)*(if k=l then 1 else 0) +
       (if i=k then 1 else 0)*(if j=l then 1 else 0) +
       (if i=l then 1 else 0)*(if j=k then 1 else 0)) /
        ((Fintype.card I : ℝ)*((Fintype.card I : ℝ)+2)) := by
  have h := gaussian_homogeneous_integral I 4 (fun x => x i*x j*x k*x l) (by
    intro r _ x
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring)
  rw [stdGaussian_coordinate_fourth_moment, stdGaussian_norm_fourth_moment] at h
  have hD : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  apply (eq_div_iff (mul_pos hD (by positivity)).ne').mpr
  simpa only [mul_comm] using h.symm

end CertificationGaussian
