import Lean
import CertificationGaussian.IncidentHolderContractions
import CertificationGaussian.Consumers.PauliLocalReadout
import CertificationGaussian.Consumers.CompleteMUB
noncomputable section
open MeasureTheory
namespace CertificationGaussian.Consumers
-- Zero incident edges: all six Hölder slots are constant one.
example : (∫ _ : PauliRecord, (1:ℝ) ∂pauliBasisRecords) ≤ 1 := by simp
example (x y z : PauliRecord) :
    (∫ s, recordOverlap pauliRecordedUnitVector x s^0 *
      recordOverlap pauliRecordedUnitVector y s^0 *
      recordOverlap pauliRecordedUnitVector z s^0 ∂pauliBasisRecords) ≤ 1 := by
  simpa using CertificationGaussian.IncidentHolder.incident_overlap_holder pauliBasisRecords pauliRecordedUnitVector
    pauliRecordedUnitVector_continuous (1/4) pauliBasisRecords_overlap_sixth 0 0 0
    (by norm_num) x y z
-- Repeated coordinate/neighbor: all six labeled incident edges may coincide.
example (x : PauliRecord) :
    (∫ s, recordOverlap pauliRecordedUnitVector x s^6 ∂pauliBasisRecords) ≤ 1/4 := by
  simpa only [pow_zero,mul_one,Nat.add_zero,CertificationGaussian.IncidentHolder.sixthRoot_pow_six (1/4) (by norm_num)] using
    CertificationGaussian.IncidentHolder.incident_overlap_holder pauliBasisRecords pauliRecordedUnitVector
      pauliRecordedUnitVector_continuous (1/4) pauliBasisRecords_overlap_sixth 6 0 0
      (by norm_num) x x x
example : 81*haarFourOverlapIntegral 3 mixedSixGraph ≤ 81/100 := by
  have h := haarFourOverlapIntegral_scaled_le_via_incident_holder 3 mixedSixGraph mixedSixGraph_regular_cycle.1
  norm_num [haarLocalKappa] at h ⊢
  exact h
example : 16*pauliFourOverlapIntegral mixedSixGraph ≤ pauliLocalKappa :=
  pauliFourOverlapIntegral_scaled_le_via_incident_holder _ mixedSixGraph_regular_cycle.1 mixedSixGraph_regular_cycle.2
example (d : ℕ) [NeZero d] (hd : 2≤d) (B : CompleteMUB d) :
    (d:ℝ)^4*completeMUBFourOverlapIntegral B mixedSixGraph ≤ completeMUBLocalKappa d :=
  completeMUBFourOverlapIntegral_scaled_le_via_incident_holder B hd _
    mixedSixGraph_regular_cycle.1 mixedSixGraph_regular_cycle.2
-- Disconnected multiplicities and dimensions 1 and 2 remain permitted in the Haar non-strict bound.
example (d : ℕ) [NeZero d] :
    haarFourOverlapIntegral d disconnectedSixGraph ≤ (6/((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2)))^2 :=
  haarFourOverlapIntegral_le_via_incident_holder d _ disconnectedSixGraph_regular
example : haarLocalKappa 1=1 ∧ haarLocalKappa 2=1 := haar_kappa_low_dimensions

#check haarFourOverlapIntegral_scaled_le
#check pauliFourOverlapIntegral_scaled_le
#check completeMUBFourOverlapIntegral_scaled_le
end CertificationGaussian.Consumers

open Lean Elab Command in
run_elab do
  logInfo "REGRESSION_CHECK\tIncidentHolderBoundaries\tPASS"
