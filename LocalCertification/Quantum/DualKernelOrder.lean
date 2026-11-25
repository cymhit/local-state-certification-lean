import LocalCertification.Extremal.ResidualMass
import CertificationGaussian.KernelAsymptotics

set_option autoImplicit false
open scoped BigOperators
open LocalCertification.Extremal
noncomputable section
namespace LocalCertification.Quantum

/-- The actual residual's first nonzero radius is exactly r+1, using its proved positive leading weight. -/
theorem dualResidualKernel_effectiveOrder {d : ℕ} (hd : 2 ≤ d) {r : ℕ}
    (c : IntegerDualCertificate ((d : ℝ)+1) r) :
    CertificationGaussian.effectiveKernelOrder (residualRadii c) (residualWeight d c)
      (residualWeight_mass d (by omega) c) = r+1 := by
  apply le_antisymm
  · exact CertificationGaussian.effectiveKernelOrder_le _ _ _ (first_mem_residualRadii c)
      (ne_of_gt (first_residualWeight_pos (by omega : 0 < d) c))
  · exact (Finset.mem_Icc.mp (CertificationGaussian.effectiveKernelOrder_mem _ _
      (residualWeight_mass d (by omega) c)).1).1

/-- The genuine kernelVarianceScale has the exact residual polynomial order, with positive constants. -/
theorem dualResidualKernel_power_order {d : ℕ} (hd : 2 ≤ d) {r : ℕ}
    (c : IntegerDualCertificate ((d : ℝ)+1) r) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ N : ℕ, ∀ n ≥ N,
      a/(n : ℝ)^(r+1) ≤ CertificationGaussian.kernelVarianceScale d n (residualRadii c) (residualWeight d c) ∧
      CertificationGaussian.kernelVarianceScale d n (residualRadii c) (residualWeight d c) ≤ A/(n : ℝ)^(r+1) := by
  simpa only [dualResidualKernel_effectiveOrder hd c] using
    CertificationGaussian.kernelVarianceScale_two_sided_power_order hd (residualRadii c)
      (residualWeight d c) (residualWeight_mass d (by omega) c)

end LocalCertification.Quantum
