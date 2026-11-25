import LocalCertification.Certificates.RealLowDegree
import LocalCertification.Certificates.TableValues
set_option autoImplicit false
namespace LocalCertification.Certificates.Consumers
open LocalCertification.Extremal

/-- Four low-degree critical values in the real decay-base parametrization. -/
theorem proposition_five_six :
    (∀ q : ℝ, 1<q → gamma q 0=q⁻¹) ∧
    (∀ q : ℝ, 2≤q → gamma q 1=1/(q^2+1)) ∧
    gamma 3 2=1/35 ∧
    (∀ q : ℝ, 4≤q → gamma q 2=1/(q*(q^2+3))) :=
  ⟨gamma_zero,gamma_one_real,Examples.Degree2.exact_value,gamma_two_real⟩

/-- The real-parameter degree-one result includes its endpoint. -/
theorem degree_one_endpoint : gamma 2 1=1/5 := by
  have h := gamma_one_real 2 (by norm_num)
  norm_num at h ⊢
  exact h

/-- A genuinely non-integral parameter checks the domain of the general theorem. -/
theorem degree_one_nonintegral : gamma (5/2) 1=4/29 := by
  have h := gamma_one_real (5/2) (by norm_num)
  norm_num at h ⊢
  exact h

theorem degree_two_endpoint : gamma 4 2=1/76 := by
  have h := gamma_two_real 4 (by norm_num)
  norm_num at h ⊢
  exact h

theorem degree_two_nonintegral : gamma (9/2) 2=8/837 := by
  have h := gamma_two_real (9/2) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The exceptional q=3 value prevents extending the degree-two formula below its stated range. -/
theorem degree_two_qthree_exception : gamma 3 2≠1/((3 : ℝ)*(3^2+3)) := by
  rw [Examples.Degree2.exact_value]
  norm_num

end LocalCertification.Certificates.Consumers
