import LocalCertification.Quantum.ReadoutScoreMoments
import CertificationGaussian.CompleteMUBRecords

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory CertificationGaussian
open scoped ENNReal
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ}

/-- Independently chosen complete-MUB labels followed by the actual product QIT POVM.
The basis labels and all outcomes are retained, including for entangled mixed inputs. -/
def completeMUBBornLaw (B : CompleteMUB d) (n : ℕ) (ρ : QIT.State (QuditIndex d n)) :
    Measure ((Fin n → Fin (d+1)) × QuditIndex d n) :=
  completeBornRecordLaw ρ (localProductSetting B.basis)
    (localProductSetting_continuous B.basis continuous_of_discreteTopology).measurable
    (Measure.pi (fun _ : Fin n => uniformFiniteOutcome (d+1)))

instance completeMUBBornLaw_probability (B : CompleteMUB d) (n : ℕ)
    (ρ : QIT.State (QuditIndex d n)) : IsProbabilityMeasure (completeMUBBornLaw B n ρ) := by
  unfold completeMUBBornLaw
  infer_instance

/-- The recorded basis labels have their actual state-independent product uniform law. -/
theorem completeMUBBornLaw_fst (B : CompleteMUB d) (ρ : QIT.State (QuditIndex d n)) :
    (completeMUBBornLaw B n ρ).fst=Measure.pi (fun _ : Fin n => uniformFiniteOutcome (d+1)) :=
  completeBornRecordLaw_fst ρ _ _ _

/-- Exact identification of the reference records with the ensemble used by the MUB operator proof. -/
theorem completeMUBBornReference_records [NeZero d] :
    (completeBornReference d n (Measure.pi (fun _ : Fin n => uniformFiniteOutcome (d+1)))).map
      (localRecordEquiv (Fin (d+1)) d n)=Measure.pi (fun _ : Fin n => completeMUBRecords d) :=
  localRecordEquiv_reference (uniformFiniteOutcome (d+1))

/-- The actual experiment has precisely the paper's D times Born-probability density. -/
theorem completeMUBBornLaw_density [NeZero d] (B : CompleteMUB d)
    (ρ : QIT.State (QuditIndex d n)) :
    (completeBornReference d n (Measure.pi (fun _ : Fin n => uniformFiniteOutcome (d+1)))).withDensity
      (fun z => ENNReal.ofReal ((d:ℝ)^n*productBorn d n (localProductSetting B.basis z.1) ρ z.2))=
      completeMUBBornLaw B n ρ :=
  completeBornRecordLaw_density ρ _ _ _

/-- Signed cardinality scores have the genuine first moment for every mixed state. -/
theorem completeMUBBornScore_mean [NeZero d] (B : CompleteMUB d)
    (ρ : QIT.State (QuditIndex d n)) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    ∫ z,cardinalityBornScore B.basis r lam ψ z ∂completeMUBBornLaw B n ρ=
      (Matrix.trace (ρ.matrix*cardinalityReadoutMean d (completeMUBRecords d)
        (completeMUBFullRecord B) r lam ((d:ℝ)^n) ψ.ofLp)).re :=
  cardinalityBornScore_mean B.basis continuous_of_discreteTopology (uniformFiniteOutcome (d+1)) ρ r lam ψ

/-- The second moment is the full original M, with the same complete records and signed score. -/
theorem completeMUBBornScore_second [NeZero d] (B : CompleteMUB d)
    (ρ : QIT.State (QuditIndex d n)) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    ∫ z,(cardinalityBornScore B.basis r lam ψ z)^2 ∂completeMUBBornLaw B n ρ=
      (Matrix.trace (ρ.matrix*cardinalityReadoutSecond d (completeMUBRecords d)
        (completeMUBFullRecord B) r lam ((d:ℝ)^n) ψ.ofLp)).re :=
  cardinalityBornScore_second B.basis continuous_of_discreteTopology (uniformFiniteOutcome (d+1)) ρ r lam ψ

/-- Square integrability is obtained from the implemented score, without a moment premise. -/
theorem completeMUBBornScore_memLp (B : CompleteMUB d)
    (ρ : QIT.State (QuditIndex d n)) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    MemLp (cardinalityBornScore B.basis r lam ψ) 2 (completeMUBBornLaw B n ρ) :=
  cardinalityBornScore_memLp B.basis continuous_of_discreteTopology (uniformFiniteOutcome (d+1)) ρ r lam ψ

/-- All mixed inputs obey the original full-M variance bound. -/
theorem completeMUBBornScore_variance_le [NeZero d] (B : CompleteMUB d)
    (ρ : QIT.State (QuditIndex d n)) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    variance (cardinalityBornScore B.basis r lam ψ) (completeMUBBornLaw B n ρ)≤
      (Matrix.trace (ρ.matrix*cardinalityReadoutSecond d (completeMUBRecords d)
        (completeMUBFullRecord B) r lam ((d:ℝ)^n) ψ.ofLp)).re :=
  cardinalityBornScore_variance_le B.basis continuous_of_discreteTopology (uniformFiniteOutcome (d+1)) ρ r lam ψ

end LocalCertification.Quantum
