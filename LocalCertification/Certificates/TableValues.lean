import LocalCertification.Certificates.Consumers
import LocalCertification.Certificates.Examples.Degree2
import LocalCertification.Certificates.Examples.Degree3
import LocalCertification.Certificates.Examples.Degree4
import LocalCertification.Certificates.Examples.Degree5
import LocalCertification.Certificates.Examples.Degree6
import LocalCertification.Certificates.Examples.Degree7
import LocalCertification.Certificates.Examples.Degree8
import LocalCertification.Certificates.Examples.Degree9
import LocalCertification.Certificates.Examples.Degree10

set_option autoImplicit false
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Examples

/-- Exact degree-zero-through-ten values, derived from kernel-checked finite certificates. -/
theorem critical_values_zero_through_ten :
    gamma 3 0=1/3 ∧ gamma 3 1=1/10 ∧ gamma 3 2=1/35 ∧ gamma 3 3=4/427 ∧
    gamma 3 4=5/1744 ∧ gamma 3 5=35/38672 ∧ gamma 3 6=8/27667 ∧
    gamma 3 7=1232/13932665 ∧ gamma 3 8=286/9700391 ∧
    gamma 3 9=5005/539669854 ∧ gamma 3 10=3536/1153439109 :=
  ⟨Consumers.degree_zero_exact_certificate.2.2,Consumers.degree_one_exact_value,
    Degree2.exact_value,Degree3.exact_value,Degree4.exact_value,Degree5.exact_value,
    Degree6.exact_value,Degree7.exact_value,Degree8.exact_value,Degree9.exact_value,Degree10.exact_value⟩

/-- The exact degree-four normalized extremal polynomial. -/
noncomputable def quarticPolynomial : ℚ[X] :=
  C (1/5232)*(X-2)*(X-4)*(C 143*X^2-C 782*X+C 654)

theorem quartic_normalized_numerator :
    (((Polynomial.ofFn 5 Degree4.data.2.1).eval 0)⁻¹ • Polynomial.ofFn 5 Degree4.data.2.1)=quarticPolynomial := by
  apply Polynomial.funext
  intro x
  norm_num [Degree4.data,Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_succ,
    Polynomial.eval_smul,quarticPolynomial]
  ring

theorem quartic_unique_optimizer :
    admissible 4 (quarticPolynomial.map (Rat.castHom ℝ)) ∧
    envelopeRatio 3 (quarticPolynomial.map (Rat.castHom ℝ))=5/1744 ∧
    ∀ P : ℝ[X], admissible 4 P → envelopeRatio 3 P=gamma 3 4 →
      P=quarticPolynomial.map (Rat.castHom ℝ) := by
  have h := certificateCheck_sound 3 (by norm_num) 4 Degree4.data Degree4.certificate_passes
  have hn := rational_normalization_of_attainment 3 (by norm_num) 4 _ _
    (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)) h.1 h.2.1
  rw [quartic_normalized_numerator] at hn
  norm_num only [Rat.cast_ofNat] at hn
  exact ⟨hn.2.1,hn.2.2.1.trans Degree4.exact_value,hn.2.2.2⟩

theorem quartic_positive_tail_array :
    (5232 : ℚ) • shiftedPolynomial quarticPolynomial 7=
      Polynomial.ofFn 5 ![32805,35796,14092,2364,143] := by
  apply Polynomial.funext
  intro x
  norm_num [quarticPolynomial,shiftedPolynomial,Polynomial.eval_comp,
    Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_succ,Polynomial.eval_smul]
  ring

theorem quartic_difference_tail_array :
    (5232 : ℚ) • shiftedPolynomial (weightedDifference 3 quarticPolynomial) 7=
      Polynomial.ofFn 5 ![13215,35744,20234,4156,286] := by
  apply Polynomial.funext
  intro x
  norm_num [quarticPolynomial,shiftedPolynomial,weightedDifference,Polynomial.eval_comp,
    Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_succ,Polynomial.eval_smul]
  ring

end LocalCertification.Certificates.Examples
