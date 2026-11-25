import LocalCertification.Certificates.DimensionValues
import LocalCertification.Extremal.ParityEnvelopes

set_option autoImplicit false
open Polynomial LocalCertification LocalCertification.Manuscript

example : Manuscript.gamma (1/2) 0 = 2/3 := by
  norm_num [Manuscript.gamma_zero (1/2) (by norm_num)]

example (d : ℝ) (hd : 0 < d) : criticalDegree d (Manuscript.gamma d 0) = 1 :=
  criticalDegree_at_critical_value d hd 0

example (d b : ℝ) (hd : 0 < d) (hb : b < 1) :
    criticalDegree d ((1 - b) / (1 - b)) = 0 :=
  criticalDegree_at_unit_fidelity d hd b hb

example (d : ℝ) (hd : 0 < d) (p : ℝ[X]) (hp : Extremal.admissible 0 p)
    (hopt : Extremal.envelopeRatio (d + 1) p = Manuscript.gamma d 0) :
    (ell d p, u d p) = (0, (d + 1)⁻¹) := by
  simpa only [Manuscript.gamma_zero d hd] using
    optimizer_endpoints_even d hd 0 ⟨0, rfl⟩ p hp hopt

#check LocalCertification.Manuscript.sharp_order_and_inversion
#check LocalCertification.Manuscript.optimizer_endpoints_odd
#check LocalCertification.Manuscript.quartic_interpolation
#check LocalCertification.Manuscript.quartic_envelope_bound
#check LocalCertification.Manuscript.qubit_quadratic_ratio_antitone
#check LocalCertification.Manuscript.qubit_quadratic_endpoints
#check LocalCertification.Manuscript.qubit_critical_values

#eval IO.println "DimensionCriticalValues_PASS"
