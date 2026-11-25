import CertificationGaussian.LocalHaarTwirl
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section
open MeasureTheory Metric Set
open scoped BigOperators ENNReal
namespace CertificationGaussian

/-- The actual uniform outcome measure, independently defined by normalized counting. -/
def uniformFiniteOutcome (d : Nat) : Measure (Fin d) := (d : ℝ≥0∞)⁻¹ • Measure.count

instance uniformFiniteOutcome_probability (d : Nat) [NeZero d] :
    IsProbabilityMeasure (uniformFiniteOutcome d) where
  measure_univ := by
    simp [uniformFiniteOutcome, Measure.smul_apply, ENNReal.inv_mul_cancel,
      show (d : ℝ≥0∞) ≠ 0 by exact_mod_cast NeZero.ne d]

/-- Complete records retain both the full Haar basis and the independent uniform outcome. -/
def haarBasisRecords (d : Nat) : Measure (ComplexUnitary (Fin d) × Fin d) :=
  (complexUnitaryHaar (Fin d)).prod (uniformFiniteOutcome d)

instance haarBasisRecords_probability (d : Nat) [NeZero d] :
    IsProbabilityMeasure (haarBasisRecords d) := by
  unfold haarBasisRecords
  infer_instance

theorem uniformFiniteOutcome_integral (d : Nat) (f : Fin d → ℂ) :
    ∫ j, f j ∂uniformFiniteOutcome d = (d : ℂ)⁻¹ * ∑ j, f j := by
  rw [uniformFiniteOutcome, integral_smul_measure, integral_count]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]

theorem haarBasisRecords_integrable (d : Nat) [NeZero d]
    (f : ComplexUnitary (Fin d) × Fin d → ℂ) (hf : Continuous f) :
    Integrable f (haarBasisRecords d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The factor d in the paper comes from the genuine uniform outcome probability. -/
theorem haarBasisRecords_scaled_integral (d : Nat) [NeZero d]
    (f : ComplexUnitary (Fin d) × Fin d → ℂ) (hf : Continuous f) :
    (d : ℂ) * ∫ ω, f ω ∂haarBasisRecords d =
      ∫ U, ∑ j, f (U,j) ∂complexUnitaryHaar (Fin d) := by
  rw [haarBasisRecords, integral_prod _ (haarBasisRecords_integrable d f hf)]
  simp_rw [uniformFiniteOutcome_integral]
  rw [integral_const_mul]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

/-- The real projector attached to a full basis/outcome record. -/
def recordedProjector (d : Nat) (ω : ComplexUnitary (Fin d) × Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  columnProjector (Fin d) ω.1.val ω.2

@[fun_prop] theorem recordedProjector_entry_continuous (d : Nat) (a b : Fin d) :
    Continuous (fun ω => recordedProjector d ω a b) := by
  apply continuous_prod_of_discrete_right.mpr
  intro j
  unfold recordedProjector columnProjector
  fun_prop

@[fun_prop] theorem recordedProjector_trace_continuous (d : Nat)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun ω => Matrix.trace (recordedProjector d ω*A)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  fun_prop

@[fun_prop] theorem recordedComplement_trace_continuous (d : Nat)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun ω => Matrix.trace ((1-recordedProjector d ω)*A)) := by
  simp only [Matrix.sub_mul, one_mul, Matrix.trace_sub]
  fun_prop

/-- First moment with the complete Haar-basis/uniform-outcome records and exact factor d. -/
theorem haarBasisRecords_projector_mean (d : Nat) [NeZero d] (a b : Fin d) :
    (d : ℂ)*∫ ω, recordedProjector d ω a b ∂haarBasisRecords d =
      (1 : Matrix (Fin d) (Fin d) ℂ) a b := by
  rw [haarBasisRecords_scaled_integral d _ (recordedProjector_entry_continuous d a b)]
  have he (U : ComplexUnitary (Fin d)) :
      ∑ j, recordedProjector d (U,j) a b = (1 : Matrix (Fin d) (Fin d) ℂ) a b := by
    change (∑ j, columnProjector (Fin d) U.val j a b) = _
    rw [← Matrix.sum_apply, sum_columnProjector]
  simp_rw [he]
  simp

/-- The success twirl in the paper, as an integral over full basis/outcome records. -/
theorem haarBasisRecords_success (d : Nat) [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    (d : ℂ)*∫ ω, recordedProjector d ω a b*Matrix.trace (recordedProjector d ω*A)
      ∂haarBasisRecords d = (A a b + if a=b then Matrix.trace A else 0)/((d:ℂ)+1) := by
  rw [haarBasisRecords_scaled_integral d _ (by fun_prop)]
  have he (U : ComplexUnitary (Fin d)) :
      ∑ j, recordedProjector d (U,j) a b*Matrix.trace (recordedProjector d (U,j)*A) =
        unitaryDephasing (Fin d) U.val A a b := by
    rw [unitaryDephasing_eq_projector_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, recordedProjector]
    simp only [mul_comm]
  simp_rw [he]
  simpa only [Fintype.card_fin] using haar_unitaryDephasing_entry (Fin d) A a b

/-- The failure/complement twirl, on precisely the same basis/outcome record probability. -/
theorem haarBasisRecords_complement (d : Nat) [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    (d : ℂ)*∫ ω, recordedProjector d ω a b*Matrix.trace ((1-recordedProjector d ω)*A)
      ∂haarBasisRecords d =
      (((d:ℂ)*Matrix.trace A)*(if a=b then 1 else 0)-A a b)/((d:ℂ)+1) := by
  rw [haarBasisRecords_scaled_integral d _ (by fun_prop)]
  have he (U : ComplexUnitary (Fin d)) :
      ∑ j, recordedProjector d (U,j) a b*Matrix.trace ((1-recordedProjector d (U,j))*A) =
        unitaryComplementDephasing (Fin d) U.val A a b := by
    simp only [unitaryComplementDephasing, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, recordedProjector]
    simp only [mul_comm]
  simp_rw [he]
  simpa only [Fintype.card_fin] using haar_unitaryComplementDephasing_entry (Fin d) A a b

/-- Explicit integrability of the two actual record integrands, not an assumed moment field. -/
theorem haarBasisRecords_twirl_integrable (d : Nat) [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    Integrable (fun ω => recordedProjector d ω a b*Matrix.trace (recordedProjector d ω*A))
      (haarBasisRecords d) ∧
    Integrable (fun ω => recordedProjector d ω a b*Matrix.trace ((1-recordedProjector d ω)*A))
      (haarBasisRecords d) :=
  ⟨haarBasisRecords_integrable d _ (by fun_prop), haarBasisRecords_integrable d _ (by fun_prop)⟩

end CertificationGaussian
