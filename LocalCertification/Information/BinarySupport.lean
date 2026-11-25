import LocalCertification.Information.ExponentialSupport
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal BigOperators Topology
noncomputable section
namespace LocalCertification.Information

/-- The two-atom affine KL support; p and q are probabilities of accepting the source. -/
def binarySupport (t p q : ℝ) : ℝ :=
  t * (2 * p - 1) - (Real.exp t - 1) * q - (Real.exp (-t) - 1) * (1 - q)

theorem binarySupport_continuous (t : ℝ) : Continuous (fun z : ℝ × ℝ => binarySupport t z.1 z.2) := by
  unfold binarySupport
  fun_prop

/-- A measurable event provides a full singular KL lower support by actual binary data processing. -/
theorem binarySupport_le_klDiv {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set X) (hA : MeasurableSet A) (t : ℝ) :
    ENNReal.ofReal (binarySupport t (P.real A) (Q.real A)) ≤ klDiv P Q := by
  classical
  let f : X → Fin 2 := fun x => if x ∈ A then 0 else 1
  have hf : Measurable f := Measurable.ite hA measurable_const measurable_const
  have h0 : f ⁻¹' ({0} : Set (Fin 2)) = A := by ext x; simp [f]
  have h1 : f ⁻¹' ({1} : Set (Fin 2)) = Aᶜ := by ext x; simp [f]
  have h := finite_klDiv_exponential_support (P.map f) (Q.map f)
    (fun i : Fin 2 => if i = 0 then t else -t)
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.sum_univ_two, ite_true, hone, ite_false, Measure.map_apply hf (measurableSet_singleton _), h0, h1] at h
  have hp : (P Aᶜ).toReal = 1 - P.real A := probReal_compl_eq_one_sub hA
  have hq : (Q Aᶜ).toReal = 1 - Q.real A := probReal_compl_eq_one_sub hA
  rw [hp, hq] at h
  have he : t * (P A).toReal - (Real.exp t - 1) * (Q A).toReal +
      (-t * (1 - P.real A) - (Real.exp (-t) - 1) * (1 - Q.real A)) =
      binarySupport t (P.real A) (Q.real A) := by unfold binarySupport Measure.real; ring
  rw [he] at h
  exact h.trans (klDiv_map_le P Q hf)

/-- The support is increasing in source acceptance and decreasing in target acceptance. -/
theorem binarySupport_mono (t p p₀ q q₀ : ℝ) (ht : 0 ≤ t) (hp : p₀ ≤ p) (hq : q ≤ q₀) :
    binarySupport t p₀ q₀ ≤ binarySupport t p q := by
  have he : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
  have h₁ := mul_le_mul_of_nonneg_left hp ht
  have h₂ := mul_le_mul_of_nonpos_left hq (sub_nonpos.mpr he)
  unfold binarySupport
  nlinarith

/-- The positive binary testing constant for error strictly below one half. -/
def testingThreshold (δ : ℝ) : ℝ := (1 - 2 * δ) * Real.log ((1 - δ) / δ)

theorem testing_parameter_pos (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1 / 2) :
    0 < Real.log ((1 - δ) / δ) := by
  apply Real.log_pos
  exact (lt_div_iff₀ hδ).mpr (by linarith)

theorem testingThreshold_pos (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1 / 2) :
    0 < testingThreshold δ := mul_pos (by linarith) (testing_parameter_pos δ hδ hhalf)

theorem binarySupport_at_error (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1 / 2) :
    binarySupport (Real.log ((1 - δ) / δ)) (1 - δ) δ = testingThreshold δ := by
  have hd : 0 < 1 - δ := by linarith
  rw [binarySupport, Real.exp_log (div_pos hd hδ), Real.exp_neg,
    Real.exp_log (div_pos hd hδ)]
  unfold testingThreshold
  field_simp
  ring

/-- Endpoint errors give the usual strictly positive threshold without differentiating boundary KL. -/
theorem testingThreshold_le_binarySupport (δ p q : ℝ) (hδ : 0 < δ) (hhalf : δ < 1 / 2)
    (hp : 1 - δ ≤ p) (hq : q ≤ δ) :
    testingThreshold δ ≤ binarySupport (Real.log ((1 - δ) / δ)) p q := by
  rw [← binarySupport_at_error δ hδ hhalf]
  exact binarySupport_mono _ _ _ _ _ (testing_parameter_pos δ hδ hhalf).le hp hq

end LocalCertification.Information
