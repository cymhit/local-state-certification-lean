import LocalCertification.Quantum.BornMeasure

set_option autoImplicit false
open MeasureTheory InformationTheory LocalCertification.Quantum
open scoped ENNReal BigOperators
noncomputable section
namespace LocalCertification.Information

/-- A positive multiplicative denominator lower bound gives a dimension-free chi-square bound.
Zero numerator atoms are allowed; only the actual denominator atoms are required positive. -/
theorem finite_chiSq_le_of_domination {O : Type*} [Fintype O]
    (p q : O → ℝ) (hp : ∀ x,0≤p x) (hq : ∀ x,0<q x)
    (hp1 : ∑ x,p x=1) (hq1 : ∑ x,q x=1)
    (t : ℝ) (ht : 0<t) (hdom : ∀ x,t*p x≤q x) :
    (∑ x,(p x-q x)^2/q x)≤2/t+2 := by
  have hpoint (x : O) : (p x-q x)^2/q x≤2*(p x/t)+2*q x := by
    have hd : (p x)^2/q x≤p x/t := by
      apply (div_le_div_iff₀ (hq x) ht).mpr
      nlinarith [mul_le_mul_of_nonneg_left (hdom x) (hp x)]
    have hs : (p x-q x)^2≤2*(p x)^2+2*(q x)^2 := by
      nlinarith [sq_nonneg (p x+q x)]
    calc
      _ ≤ (2*(p x)^2+2*(q x)^2)/q x := div_le_div_of_nonneg_right hs (hq x).le
      _ = 2*((p x)^2/q x)+2*q x := by field_simp
      _ ≤ _ := by linarith
  calc
    _ ≤ ∑ x, (2*(p x/t)+2*q x) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = 2/t+2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_div,hp1,hq1]
      ring

/-- The actual product-basis Measure KL has the same dimension-free domination bound. -/
theorem productBornMeasure_klDiv_le_domination (d n : ℕ)
    (U : Fin n → CertificationGaussian.LocalUnitary d)
    (ρ σ : QIT.State (CertificationGaussian.QuditIndex d n)) (t : ℝ) (ht : 0<t)
    (hpos : ∀ x,0<productBorn d n U σ x)
    (hdom : ∀ x,t*productBorn d n U ρ x≤productBorn d n U σ x) :
    klDiv (productBornMeasure d n U ρ) (productBornMeasure d n U σ)≤ENNReal.ofReal (2/t+2) := by
  have h := finite_klDiv_le_chiSq (productBornMeasure d n U ρ) (productBornMeasure d n U σ)
    (by simpa only [productBornMeasure_atom_real] using hpos)
  simp only [productBornMeasure_atom_real] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (finite_chiSq_le_of_domination _ _
    (productBorn_nonneg d n U ρ) hpos (productBorn_sum d n U ρ) (productBorn_sum d n U σ) t ht hdom))

end LocalCertification.Information
