import CertificationGaussian.SphereTransport
import CertificationGaussian.Model

noncomputable section
open MeasureTheory ProbabilityTheory Metric
namespace CertificationGaussian.Consumers

/-- Actual normalized complex coordinates in dimension d^n have canonical sphere probability. -/
theorem qudit_gaussian_direction_law {d n : Nat} (hd : 2 ≤ d)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :
    (pairedGaussian (QuditIndex d n)).map
      (fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) =
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  exact complexGaussian_direction_map (QuditIndex d n) e₀

/-- The actual random complex vector is nonzero almost everywhere. -/
theorem qudit_gaussian_nonzero_ae {d n : Nat} (hd : 2 ≤ d) :
    ∀ᵐ x ∂pairedGaussian (QuditIndex d n), complexGaussianLift (QuditIndex d n) x ≠ 0 := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  rw [ae_iff]
  simpa only [not_not] using complexGaussianLift_zero_null (QuditIndex d n)

/-- Zero qudits is a complex line, including formal local dimension zero. -/
theorem zero_qudits_direction_law (d : Nat)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d 0)) 1) :
    (pairedGaussian (QuditIndex d 0)).map
      (fun x => sphereDirection e₀ (complexGaussianLift (QuditIndex d 0) x)) =
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d 0)) := by
  let : Nonempty (QuditIndex d 0) := ⟨Fin.elim0⟩
  exact complexGaussian_direction_map (QuditIndex d 0) e₀

end CertificationGaussian.Consumers
