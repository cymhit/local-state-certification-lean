import LocalCertification.Certificates.QubitQuadratic
import LocalCertification.Certificates.QuarticInterpolation
import LocalCertification.Certificates.RealLowDegreeConsumers

/-! # Low-degree critical values in the dimension convention -/

set_option autoImplicit false
namespace LocalCertification.Manuscript

theorem gamma_one (d : ℝ) (hd : 1 ≤ d) :
    gamma d 1 = 1 / ((d + 1) ^ 2 + 1) :=
  Certificates.gamma_one_real (d + 1) (by linarith)

theorem gamma_two (d : ℝ) (hd : 3 ≤ d) :
    gamma d 2 = 1 / ((d + 1) * ((d + 1) ^ 2 + 3)) :=
  Certificates.gamma_two_real (d + 1) (by linarith)

/-- The eleven exact qubit values; degrees two and four use the explicit
root-ratio and interpolation arguments, respectively. -/
theorem qubit_critical_values :
    gamma 2 0 = 1/3 ∧ gamma 2 1 = 1/10 ∧ gamma 2 2 = 1/35 ∧
    gamma 2 3 = 4/427 ∧ gamma 2 4 = 5/1744 ∧ gamma 2 5 = 35/38672 ∧
    gamma 2 6 = 8/27667 ∧ gamma 2 7 = 1232/13932665 ∧ gamma 2 8 = 286/9700391 ∧
    gamma 2 9 = 5005/539669854 ∧ gamma 2 10 = 3536/1153439109 := by
  obtain ⟨_, _, _, h3, _, h5, h6, h7, h8, h9, h10⟩ :=
    Certificates.Examples.critical_values_zero_through_ten
  refine ⟨?_, ?_, qubit_quadratic_exact, ?_, qubit_quartic_exact, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [gamma_zero 2 (by norm_num)]
  · norm_num [gamma_one 2 (by norm_num)]
  all_goals norm_num only [gamma, show (2 : ℝ) + 1 = 3 by norm_num]
  all_goals assumption

end LocalCertification.Manuscript
