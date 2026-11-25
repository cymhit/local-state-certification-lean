import LocalCertification.Extremal.RationalExtremizer

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace LocalCertification.Extremal

def positiveCoefficientMass {n : ℕ} (μ : Fin n → ℝ) : ℝ := ∑ i, max (μ i) 0

def negativeCoefficientMass {n : ℕ} (μ : Fin n → ℝ) : ℝ := ∑ i, max (-μ i) 0

theorem coefficient_mass_identities {n : ℕ} (μ : Fin n → ℝ) :
    2*positiveCoefficientMass μ = (∑ i, |μ i|)+(∑ i, μ i) ∧
    positiveCoefficientMass μ-negativeCoefficientMass μ = ∑ i, μ i := by
  have hp (a : ℝ) : 2*max a 0 = |a|+a := by
    by_cases h : 0 ≤ a
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · have h' : a ≤ 0 := le_of_not_ge h
      rw [max_eq_right h', abs_of_nonpos h']; ring
  have hn (a : ℝ) : max a 0-max (-a) 0 = a := by
    by_cases h : 0 ≤ a
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    · have h' : a ≤ 0 := le_of_not_ge h
      rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]; ring
  constructor
  · simp only [positiveCoefficientMass, Finset.mul_sum, hp, Finset.sum_add_distrib]
  · simp only [positiveCoefficientMass, negativeCoefficientMass, ← Finset.sum_sub_distrib, hn]

/-- Positive and negative coefficient masses of any true optimal finite dual. -/
theorem finite_dual_positive_negative_mass {n : ℕ} (q : ℝ) (hq : 1 < q) (r : ℕ)
    (x : Fin n → OnePoint ℕ) (μ : Fin n → ℝ)
    (he : ∀ b : CoeffSpace r, extrapolation r b =
      ∑ i, μ i * polynomialNode q b.1 (coefficientPolynomial b) (x i))
    (hv : ∑ i, |μ i| = extremalValue q r) :
    positiveCoefficientMass μ = (gamma q r)⁻¹ ∧
      negativeCoefficientMass μ = (gamma q r)⁻¹-1 := by
  have hm := finite_dual_mass q r x μ he
  have hi := coefficient_mass_identities μ
  rw [hv, hm] at hi
  have hpos : positiveCoefficientMass μ = (gamma q r)⁻¹ := by
    rw [gamma_eq_extremalValue q hq r, inv_div]
    exact (eq_div_iff (by norm_num : (2:ℝ) ≠ 0)).mpr (by linarith [hi.1])
  exact ⟨hpos, by linarith [hi.2]⟩

end LocalCertification.Extremal
