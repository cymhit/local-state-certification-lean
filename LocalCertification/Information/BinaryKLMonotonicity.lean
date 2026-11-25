import LocalCertification.Probability.BinaryKLLowerSemicontinuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false
open MeasureTheory InformationTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace LocalCertification.Information

/-- Expanded binary relative entropy; this expression is continuous in the source
even at zero and one, with the convention `0 log 0 = 0`. -/
def binaryRelativeEntropy (p q : ℝ) : ℝ :=
  p * Real.log p + (1-p) * Real.log (1-p) - p * Real.log q - (1-p) * Real.log (1-q)

theorem binaryRelativeEntropy_source_continuous (q : ℝ) :
    Continuous (fun p => binaryRelativeEntropy p q) := by
  unfold binaryRelativeEntropy
  exact ((Real.continuous_mul_log.add (Real.continuous_mul_log.comp
    (continuous_const.sub continuous_id))).sub (continuous_id.mul continuous_const)).sub
      ((continuous_const.sub continuous_id).mul continuous_const)

theorem binaryRelativeEntropy_deriv_source (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun x => binaryRelativeEntropy x q)
      (Real.log p - Real.log (1-p) - Real.log q + Real.log (1-q)) p := by
  convert (((Real.hasDerivAt_mul_log hp.ne').add
    ((Real.hasDerivAt_mul_log (sub_pos.mpr hp1).ne').comp p
      ((hasDerivAt_id p).const_sub 1))).sub
        ((hasDerivAt_id p).mul_const (Real.log q))).sub
          (((hasDerivAt_id p).const_sub 1).mul_const (Real.log (1-q))) using 1 <;>
    first | rfl | ring

theorem binaryRelativeEntropy_deriv_target (p q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun y => binaryRelativeEntropy p y) ((q-p)/(q*(1-q))) q := by
  convert ((hasDerivAt_const q (p * Real.log p + (1-p) * Real.log (1-p))).sub
    ((Real.hasDerivAt_log hq.ne').const_mul p)).sub
      (((Real.hasDerivAt_log (sub_pos.mpr hq1).ne').comp q
        ((hasDerivAt_id q).const_sub 1)).const_mul (1-p)) using 1
  · rfl
  · field_simp [hq.ne', (sub_pos.mpr hq1).ne']
    ring

/-- The source partial derivative in the paper's single-logarithm form. -/
theorem binaryRelativeEntropy_deriv_source_paper (p q : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x => binaryRelativeEntropy x q)
      (Real.log (p * (1-q) / (q * (1-p)))) p := by
  convert binaryRelativeEntropy_deriv_source p q hp hp1 using 1
  rw [Real.log_div (mul_ne_zero hp.ne' (sub_pos.mpr hq1).ne')
    (mul_ne_zero hq.ne' (sub_pos.mpr hp1).ne'),
    Real.log_mul hp.ne' (sub_pos.mpr hq1).ne',
    Real.log_mul hq.ne' (sub_pos.mpr hp1).ne']
  ring

theorem binaryRelativeEntropy_mono_source (q a : ℝ) (hq : 0 < q) (hqa : q ≤ a) :
    MonotoneOn (fun p => binaryRelativeEntropy p q) (Icc a 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (binaryRelativeEntropy_source_continuous q).continuousOn
    (f' := fun p => Real.log (p * (1-q) / (q * (1-p))))
  · intro p hp
    rw [interior_Icc] at hp
    exact (binaryRelativeEntropy_deriv_source_paper p q
      (hq.trans_le (hqa.trans hp.1.le)) hp.2 hq (hqa.trans_lt (hp.1.trans hp.2))).hasDerivWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    have hqp := hqa.trans hp.1.le
    apply Real.log_nonneg
    apply (le_div_iff₀ (mul_pos hq (sub_pos.mpr hp.2))).mpr
    nlinarith

theorem binaryRelativeEntropy_anti_target (p a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hbp : b ≤ p) : AntitoneOn (fun q => binaryRelativeEntropy p q) (Icc a b) := by
  have hd (q : ℝ) (hq : q ∈ Icc a b) :=
    binaryRelativeEntropy_deriv_target p q (ha.trans_le hq.1) (hq.2.trans_lt hb)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (f' := fun q => (q-p)/(q*(1-q)))
  · intro q hq
    exact (hd q (interior_subset hq)).hasDerivWithinAt
  · intro q hq
    have h := interior_subset hq
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (h.2.trans hbp))
      (mul_nonneg (ha.trans_le h.1).le (sub_nonneg.mpr (h.2.trans hb.le)))

theorem binary_klDiv_eq_binaryRelativeEntropy (p q : Icc (0 : ℝ) 1)
    (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    klDiv (binaryMeasure p) (binaryMeasure q) = ENNReal.ofReal (binaryRelativeEntropy p q) := by
  rw [binary_klDiv_formula p q hq hq1]
  congr 1
  by_cases hp : (p : ℝ) = 0
  · simp [binaryRelativeEntropy, hp]
  by_cases hp1 : (p : ℝ) = 1
  · simp [binaryRelativeEntropy, hp1]
  rw [Real.log_div hp hq.ne', Real.log_div (sub_ne_zero.mpr (Ne.symm hp1)) (sub_pos.mpr hq1).ne']
  unfold binaryRelativeEntropy
  ring

theorem binaryRelativeEntropy_at_error (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2) :
    binaryRelativeEntropy (1-δ) δ = testingThreshold δ := by
  rw [testingThreshold, Real.log_div (by linarith) hδ.ne']
  unfold binaryRelativeEntropy
  simp only [sub_sub_cancel]
  ring

/-- The source-one endpoint is included through continuity on the closed interval;
the zero-target endpoint retains its singular infinite KL. Both partial derivatives
are used to move the two error probabilities to the exact paper threshold. -/
theorem testingThreshold_le_binary_klDiv_via_derivatives (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2)
    (p q : Icc (0 : ℝ) 1) (hp : 1-δ ≤ (p : ℝ)) (hq : (q : ℝ) ≤ δ) :
    ENNReal.ofReal (testingThreshold δ) ≤ klDiv (binaryMeasure p) (binaryMeasure q) := by
  by_cases hq0 : (q : ℝ) = 0
  · rw [binary_klDiv_target_zero p q (by linarith) hq0]
    exact le_top
  have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hq0)
  rw [binary_klDiv_eq_binaryRelativeEntropy p q hqpos (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  rw [← binaryRelativeEntropy_at_error δ hδ hhalf]
  exact ((binaryRelativeEntropy_anti_target (1-δ) q δ hqpos (by linarith) (by linarith))
    ⟨le_rfl, hq⟩ ⟨hq, le_rfl⟩ hq).trans
      ((binaryRelativeEntropy_mono_source q (1-δ) hqpos (by linarith))
        ⟨le_rfl, by linarith⟩ ⟨hp, p.property.2⟩ hp)

end LocalCertification.Information

