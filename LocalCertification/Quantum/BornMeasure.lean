import LocalCertification.Quantum.ProductMeasurement
import LocalCertification.Information.FiniteKL
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory InformationTheory Matrix
noncomputable section
namespace LocalCertification.Quantum

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

/-- The complete QIT Born outcome law as a genuine probability mass function. -/
def povmBornPMF (M : QIT.POVM O I) (ρ : QIT.State I) : PMF O :=
  PMF.ofFintype (fun x => (M.prob ρ x : ℝ≥0∞)) (by exact_mod_cast M.sum_prob ρ)

variable [MeasurableSpace O] [MeasurableSingletonClass O]

def povmBornMeasure (M : QIT.POVM O I) (ρ : QIT.State I) : Measure O :=
  (povmBornPMF M ρ).toMeasure

instance povmBornMeasure_probability (M : QIT.POVM O I) (ρ : QIT.State I) :
    IsProbabilityMeasure (povmBornMeasure M ρ) := by unfold povmBornMeasure; infer_instance

@[simp] theorem povmBornMeasure_atom (M : QIT.POVM O I) (ρ : QIT.State I) (x : O) :
    povmBornMeasure M ρ {x} = (M.prob ρ x : ℝ≥0∞) :=
  (povmBornPMF M ρ).toMeasure_apply_singleton x (measurableSet_singleton x)

@[simp] theorem povmBornMeasure_atom_real (M : QIT.POVM O I) (ρ : QIT.State I) (x : O) :
    (povmBornMeasure M ρ {x}).toReal = (M.prob ρ x : ℝ) := by simp

/-- The actual product-basis readout measure; its atoms are exactly the existing QIT Born probabilities. -/
def productBornMeasure (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : Measure (CertificationGaussian.QuditIndex d n) :=
  povmBornMeasure (productBasisPOVM d n U) ρ

instance productBornMeasure_probability (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) : IsProbabilityMeasure (productBornMeasure d n U ρ) := by
  unfold productBornMeasure
  infer_instance

@[simp] theorem productBornMeasure_atom_real (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n)) (x : CertificationGaussian.QuditIndex d n) :
    (productBornMeasure d n U ρ {x}).toReal = productBorn d n U ρ x :=
  povmBornMeasure_atom_real _ _ _

/-- This is Mathlib measure KL, with no new divergence definition or positive-numerator assumption. -/
theorem productBornMeasure_klDiv_le_floor (d n : ℕ) (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) {δ : ℝ} (hδ : 0 < δ)
    (hσ : ∀ x, δ ≤ productBorn d n U σ x) :
    klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ) ≤
      ENNReal.ofReal (δ⁻¹*∑ x, (productBorn d n U ρ x-productBorn d n U σ x)^2) := by
  simpa only [productBornMeasure_atom_real] using
    LocalCertification.Information.finite_klDiv_le_floor (productBornMeasure d n U ρ)
      (productBornMeasure d n U σ) hδ (by simpa only [productBornMeasure_atom_real] using hσ)

end LocalCertification.Quantum
