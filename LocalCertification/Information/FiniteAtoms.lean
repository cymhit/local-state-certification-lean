/- Relative entropy on a finite outcome space with measurable singletons. -/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
Relative entropy on a finite outcome space with measurable singletons.
All KL values remain ENNReal.

The real atom ratio is defined as zero when its denominator is zero.
Absolute continuity proves that such atoms carry no source mass.
Joint kernels over arbitrary history spaces are treated in JointFiniteKL.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

namespace LocalCertification.Information

universe u

variable {O : Type u} [MeasurableSpace O] [Fintype O]
  [MeasurableSingletonClass O]

def atomDensity (P Q : Measure O) (o : O) : ℝ≥0∞ :=
  ENNReal.ofReal ((P {o}).toReal / (Q {o}).toReal)

def atomKL (P Q : Measure O) (o : O) : ℝ≥0∞ :=
  Q {o} * ENNReal.ofReal
    (klFun ((P {o}).toReal / (Q {o}).toReal))

omit [Fintype O] [MeasurableSingletonClass O] in
theorem atom_klFun_nonneg (P Q : Measure O) (o : O) :
    0 ≤ klFun ((P {o}).toReal / (Q {o}).toReal) :=
  klFun_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

variable {P Q : Measure O}

omit [Fintype O] [MeasurableSingletonClass O] in
theorem atomDensity_mul [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) (o : O) :
    atomDensity P Q o * Q {o} = P {o} := by
  by_cases hQ : Q {o} = 0
  · simp [atomDensity, hQ, hPQ hQ]
  · rw [atomDensity,
      ENNReal.ofReal_div_of_pos
        (ENNReal.toReal_pos hQ (measure_ne_top Q {o})),
      ENNReal.ofReal_toReal (measure_ne_top P {o}),
      ENNReal.ofReal_toReal (measure_ne_top Q {o})]
    exact ENNReal.div_mul_cancel hQ (measure_ne_top Q {o})

theorem finite_withDensity [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) :
    Q.withDensity (atomDensity P Q) = P := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul Q (measurable_of_countable _) hf,
    lintegral_fintype, lintegral_fintype]
  apply Finset.sum_congr rfl
  intro o _
  change (atomDensity P Q o * f o) * Q {o} = f o * P {o}
  calc
    (atomDensity P Q o * f o) * Q {o} =
        f o * (atomDensity P Q o * Q {o}) := by ac_rfl
    _ = f o * P {o} := by rw [atomDensity_mul hPQ]

theorem finite_klDiv_eq_sum [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) :
    klDiv P Q = ∑ o : O, atomKL P Q o := by
  have hrn := Measure.rnDeriv_withDensity Q
    (measurable_of_countable (atomDensity P Q))
  rw [finite_withDensity hPQ] at hrn
  rw [klDiv_eq_lintegral_klFun_of_ac hPQ]
  calc
    (∫⁻ o, ENNReal.ofReal (klFun (P.rnDeriv Q o).toReal) ∂Q) =
        ∫⁻ o, ENNReal.ofReal (klFun (atomDensity P Q o).toReal) ∂Q := by
      apply lintegral_congr_ae
      filter_upwards [hrn] with o ho
      rw [ho]
    _ = ∑ o : O, atomKL P Q o := by
      rw [lintegral_fintype]
      apply Finset.sum_congr rfl
      intro o _
      simp only [atomDensity, atomKL,
        ENNReal.toReal_ofReal
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
        mul_comm]

end LocalCertification.Information
