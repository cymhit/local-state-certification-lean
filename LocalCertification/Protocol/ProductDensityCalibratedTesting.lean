import LocalCertification.Protocol.ProductDensityTerminalInformation
import LocalCertification.Protocol.CalibratedTesting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter Metric LocalCertification.Information LocalCertification.Quantum LocalCertification.Extremal
open scoped ENNReal LocalCertification.Information Topology
noncomputable section
namespace LocalCertification.Protocol
universe u
variable {Z : Type u} [MeasurableSpace Z] {d n : ℕ} [NeZero d]

/-- The actual calibrated pair is used in its proved parity direction, including the critical window equality. -/
theorem calibrated_terminal_information_finite_via_product_density (hd : 2 ≤ d) (r : ℕ)
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n)) (hN : (quditDualCertificate hd r).maxNode ≤ n)
    (a b δ : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hlb : uncalibratedLowFidelity hd r ψ hN < b)
    (hgap : (a-b)/(1-b) ≤ gamma ((d : ℝ)+1) r)
    (hδ : 0 < δ) (hhalf : δ < 1 / 2) (P : QuditProtocol Z d n) (hv : Valid P ψ a b δ)
    (L : ℝ≥0∞) (hfinite : L ≠ ∞)
    (hL : ∀ U, klDiv (productBornMeasure d n U (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb))
      (productBornMeasure d n U (calibratedDenominatorState hd r ψ hN b hb0 hb1 hlb)) ≤ L) :
    ENNReal.ofReal (testingThreshold δ) ≤
      L * expectedCopies P (calibratedNumeratorState hd r ψ hN b hb0 hb1 hlb) := by
  obtain ⟨hlo,hhi⟩ := calibrated_exact_window hd r ψ hN a b hb0 hb1 hlb hgap
  dsimp only [calibratedNumeratorState, calibratedDenominatorState] at hL ⊢
  by_cases hr : Even r
  · simp only [ite_eq_left hr] at hL ⊢
    exact valid_information_low_high_finite_via_product_density P ψ a b δ hv hδ hhalf _ _ hlo.le hhi L hfinite hL
  · simp only [ite_eq_right hr] at hL ⊢
    exact valid_information_high_low_finite_via_product_density P ψ a b δ hv hδ hhalf _ _ hhi hlo.le L hfinite hL

end LocalCertification.Protocol
