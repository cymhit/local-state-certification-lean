import CertificationGaussian.Radial
import CertificationGaussian.KernelAsymptotics

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CertificationGaussian.Consumers

/-- The mean squared deviation of the normalized Gaussian radius from one is d⁻ⁿ. -/
theorem qudit_radius_second_moment {d n : Nat} (hd : 2 ≤ d) :
    ∫ x, (gaussianRadius (QuditIndex d n) x - 1)^2 ∂pairedGaussian (QuditIndex d n) =
      (d^n : ℝ)⁻¹ := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  simpa only [gaussianRadialFluctuation, qudit_card, Nat.cast_pow] using
    gaussianRadialFluctuation_second_moment (QuditIndex d n)

/-- Zero qudits means one complex coordinate, including the formally permitted d=0 edge case. -/
theorem zero_qudits_radius_second_moment (d : Nat) :
    ∫ x, (gaussianRadius (QuditIndex d 0) x - 1)^2 ∂pairedGaussian (QuditIndex d 0) = 1 := by
  let : Nonempty (QuditIndex d 0) := ⟨Fin.elim0⟩
  simpa [gaussianRadialFluctuation, qudit_card] using
    gaussianRadialFluctuation_second_moment (QuditIndex d 0)

/-- A zero weight at shell 1 does not set the decay exponent; the true order is 2. -/
theorem zero_weight_shell_order :
    effectiveKernelOrder {1,2} (fun k => if k=2 then 1 else 0) (by norm_num) = 2 := by
  norm_num [effectiveKernelOrder, effectiveKernelSupport, Finset.filter_insert, Finset.filter_singleton]

/-- Signed weights are allowed; the smallest nonzero shell is still selected. -/
theorem signed_weights_order :
    effectiveKernelOrder {1,2} (fun k => if k=1 then 2 else -1) (by norm_num) = 1 := by
  norm_num [effectiveKernelOrder, effectiveKernelSupport, Finset.filter_insert, Finset.filter_singleton]

end CertificationGaussian.Consumers
