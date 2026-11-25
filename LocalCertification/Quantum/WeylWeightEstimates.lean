import LocalCertification.Quantum.FiniteWeightBounds
import LocalCertification.Quantum.RadialWeylOrbit
import CertificationGaussian.RadialHighWeights

/-! # Finite Weyl weight estimates

The absolute mass uses every Weyl word. The square mass uses only words of
weight above the cutoff. Both masses are normalized by the Hilbert-space
dimension, and the two radial sequences share a constant independent of
the length and cutoff.
-/

set_option autoImplicit false
noncomputable section
open CertificationGaussian
open scoped BigOperators
namespace LocalCertification.Quantum

/-- The three estimates for a radial sequence evaluated on actual Weyl words. -/
def WeylWeightEstimates (d r : ℕ) [NeZero d] (a : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ L : ℕ,
    (∀ w ∈ Finset.Ioc L n, |a w| ≤ C * (n : ℝ)^r * ((d+1 : ℝ)⁻¹)^L) ∧
    ((d : ℝ)^n)⁻¹ * (∑ W : Fin n → ZMod d × ZMod d,
      |a (radialBellSupport 0 W).card|) ≤ C * (n : ℝ)^r ∧
    Real.sqrt ((∑ W : Fin n → ZMod d × ZMod d,
      if L < (radialBellSupport 0 W).card then (a (radialBellSupport 0 W).card)^2 else 0)
      / (d : ℝ)^n) ≤ C * (n : ℝ)^r * Real.sqrt (((d+1 : ℝ)⁻¹)^L)

private theorem weight_estimates_of_max_and_mass (d r : ℕ) [NeZero d] (hd : 1 ≤ d)
    (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hmax : ∀ n : ℕ, 1 ≤ n → ∀ L : ℕ, ∀ w ∈ Finset.Ioc L n,
      |a w| ≤ C * (n : ℝ)^r * ((d+1 : ℝ)⁻¹)^L)
    (hmass : ∀ n : ℕ, 1 ≤ n → ((d : ℝ)^n)⁻¹ * (∑ W : Fin n → ZMod d × ZMod d,
      |a (radialBellSupport 0 W).card|) ≤ C * (n : ℝ)^r) :
    WeylWeightEstimates d r a C := by
  intro n hn L
  refine ⟨hmax n hn L, hmass n hn, ?_⟩
  let wt (W : Fin n → ZMod d × ZMod d) := (radialBellSupport 0 W).card
  let high (W : Fin n → ZMod d × ZMod d) : ℝ := if L < wt W then a (wt W) else 0
  let A := C * (n : ℝ)^r
  let t := ((d+1 : ℝ)⁻¹)^L
  have hA : 0 ≤ A := mul_nonneg hC (by positivity)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hD : 0 < (d : ℝ)^n := by positivity
  have hbound (W) : |high W| ≤ A*t := by
    by_cases h : L < wt W
    · have hnW : wt W ≤ n := by simpa [wt] using Finset.card_le_univ (radialBellSupport 0 W)
      simpa only [high, ite_eq_left h] using hmax n hn L (wt W) (Finset.mem_Ioc.mpr ⟨h,hnW⟩)
    · simpa only [high, ite_eq_right h, abs_zero] using mul_nonneg hA ht
  have hmass' : ((d : ℝ)^n)⁻¹ * ∑ W, |high W| ≤ A := by
    apply le_trans _ (hmass n hn)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro W _
    change |if L < wt W then a (wt W) else 0| ≤ |a (wt W)|
    split_ifs <;> simp
  have hsq := finite_square_mass_le high hD (mul_nonneg hA ht) hbound hmass'
  have hroot := Real.sqrt_le_sqrt hsq
  have hprod : A*t*A = A^2*t := by ring
  rw [hprod, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA] at hroot
  convert hroot using 1
  congr 2
  apply Finset.sum_congr rfl
  intro W _
  change (if L < wt W then (a (wt W))^2 else 0) = (if L < wt W then a (wt W) else 0)^2
  split_ifs <;> simp

/-- A single constant supplies all three Weyl estimates for both radial
sequences, including cutoffs at or above the number of sites. -/
theorem weyl_weight_estimates (d r : ℕ) [NeZero d] (hd : 1 ≤ d) (lam : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧
      WeylWeightEstimates d r (radialFirstCoefficient d r lam) C ∧
      WeylWeightEstimates d r (radialSecondCoefficient d r lam) C := by
  let sq := fun j => (lam j)^2
  let B := radialCoefficientPolynomialConstant d r lam
  let A := complementLambdaCoefficient d r lam
  let Bs := radialCoefficientPolynomialConstant d r sq
  let As := complementLambdaCoefficient d r sq
  let C := 1 + B + A + 2*Bs + 2*As
  have hB : 0 ≤ B := radialCoefficientPolynomialConstant_nonneg d r lam
  have hA : 0 ≤ A := complementLambdaCoefficient_nonneg d r hd lam
  have hBs : 0 ≤ Bs := radialCoefficientPolynomialConstant_nonneg d r sq
  have hAs : 0 ≤ As := complementLambdaCoefficient_nonneg d r hd sq
  have hC : 0 < C := by dsimp only [C]; linarith
  have ha : A ≤ C := by dsimp only [C]; linarith
  have hb : B ≤ C := by dsimp only [C]; linarith
  have has' : 2*As ≤ C := by dsimp only [C]; linarith
  have hbs' : 2*Bs ≤ C := by dsimp only [C]; linarith
  have full (u : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
      ((d : ℝ)^n)⁻¹ * (∑ W : Fin n → ZMod d × ZMod d,
        |radialFirstCoefficient d r u (radialBellSupport 0 W).card|) ≤
        complementLambdaCoefficient d r u * (n : ℝ)^r := by
    have h := radialFirstCoefficient_abs_mass (S := Fin n) d r (by omega) u
      (0 : ZMod d × ZMod d) localWeylLabel_card
    simp only [Fintype.card_fin] at h
    exact h.trans (complementLambda_le_polynomial d n r hd hn u)
  refine ⟨C, hC, weight_estimates_of_max_and_mass d r hd _ C hC.le ?_ ?_,
    weight_estimates_of_max_and_mass d r hd _ C hC.le ?_ ?_⟩
  · intro n hn L w hw
    have h := (finite_high_weight_maxima d n r L hn ⟨w,hw⟩ lam).1
    exact ((Finset.le_sup' (fun v => |radialFirstCoefficient d r lam v|) hw).trans h).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity)) (by positivity))
  · intro n hn
    exact (full lam n hn).trans (mul_le_mul_of_nonneg_right ha (by positivity))
  · intro n hn L w hw
    have h := (finite_high_weight_maxima d n r L hn ⟨w,hw⟩ lam).2
    have heq : 2 * (Bs * (n : ℝ)^r * ((d+1 : ℝ)⁻¹)^L) =
        (2*Bs) * (n : ℝ)^r * ((d+1 : ℝ)⁻¹)^L := by ring
    rw [show radialCoefficientPolynomialConstant d r (fun j => (lam j)^2) = Bs from rfl, heq] at h
    exact ((Finset.le_sup' (fun v => |radialSecondCoefficient d r lam v|) hw).trans h).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbs' (by positivity)) (by positivity))
  · intro n hn
    simp only [radialSecondCoefficient, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
      ← Finset.mul_sum]
    calc
      _ = 2 * (((d : ℝ)^n)⁻¹ * ∑ W : Fin n → ZMod d × ZMod d,
        |radialFirstCoefficient d r sq (radialBellSupport 0 W).card|) := by ring
      _ ≤ 2*(As*(n : ℝ)^r) := mul_le_mul_of_nonneg_left (full sq n hn) (by norm_num)
      _ = (2*As)*(n : ℝ)^r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right has' (by positivity)

/-- Complete estimates for the first radial Weyl sequence. -/
theorem first_weyl_weight_estimates (d r : ℕ) [NeZero d] (hd : 1 ≤ d) (lam : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ WeylWeightEstimates d r (radialFirstCoefficient d r lam) C := by
  obtain ⟨C, hC, hc, _⟩ := weyl_weight_estimates d r hd lam
  exact ⟨C, hC, hc⟩

/-- Complete estimates for the second radial Weyl sequence. -/
theorem second_weyl_weight_estimates (d r : ℕ) [NeZero d] (hd : 1 ≤ d) (lam : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ WeylWeightEstimates d r (radialSecondCoefficient d r lam) C := by
  obtain ⟨C, hC, _, he⟩ := weyl_weight_estimates d r hd lam
  exact ⟨C, hC, he⟩

end LocalCertification.Quantum
