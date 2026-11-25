import CertificationGaussian.GaussianTail

noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators ENNReal
namespace CertificationGaussian
variable (I : Type*) [Fintype I]

/-- The one common radius used by every measurement basis: t=norm(z)^2/D. -/
def gaussianRadius (x : (Fin 2 × I) → ℝ) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * ∑ i, Complex.normSq (complexCoordinate x i)

def gaussianRadialFluctuation (x : (Fin 2 × I) → ℝ) : ℝ := gaussianRadius I x - 1

theorem gaussianRadius_eq_norm_sq (x : (Fin 2 × I) → ℝ) :
    gaussianRadius I x = ‖complexGaussianLift I x‖^2 / (Fintype.card I : ℝ) := by
  simp only [gaussianRadius, EuclideanSpace.norm_sq_eq, complexGaussianLift,
    Complex.normSq_eq_norm_sq, div_eq_mul_inv, mul_comm]

variable [DecidableEq I]
def radialPolynomial : MvPolynomial (Fin 2 × I) ℝ :=
  C ((Fintype.card I : ℝ)⁻¹) * ∑ i, outcomePoly (1 : Matrix I I ℂ) i

theorem radialPolynomial_degree : (radialPolynomial I).totalDegree ≤ 2 := by
  apply (degree_C_mul _ _).trans
  apply totalDegree_finsetSum_le
  intro i _
  exact degree_outcome _ i

theorem eval_radialPolynomial (x : (Fin 2 × I) → ℝ) :
    eval x (radialPolynomial I) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, radialPairOutcome (blockCoordinates I x i) := by
  simp only [radialPolynomial, map_mul, eval_C, map_sum, eval_outcome, gaussianOutcome_identity]

variable [Nonempty I]
omit [DecidableEq I] in
theorem gaussianRadialFluctuation_eq_block (x : (Fin 2 × I) → ℝ) :
    gaussianRadialFluctuation I x =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, radialPairOutcome (blockCoordinates I x i) := by
  have hD : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [gaussianRadialFluctuation, gaussianRadius, complexCoordinate_normSq,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp
  ring

theorem radialPolynomial_eval_fluctuation (x : (Fin 2 × I) → ℝ) :
    eval x (radialPolynomial I) = gaussianRadialFluctuation I x := by
  rw [eval_radialPolynomial, gaussianRadialFluctuation_eq_block]

theorem gaussianRadialFluctuation_memLp (p : ℝ) (hp : 2 ≤ p) :
    MemLp (gaussianRadialFluctuation I) (ENNReal.ofReal p) (pairedGaussian I) := by
  simpa only [radialPolynomial_eval_fluctuation] using paired_quartic_memLp I
    (radialPolynomial I) ((radialPolynomial_degree I).trans (by decide)) p hp

omit [DecidableEq I] [Nonempty I] in
private theorem block_sum_square (z : I → ℝ × ℝ) :
    (∑ i, radialPairOutcome (z i))^2 = blockQuadratic (fun _ _ : I => 1) z := by
  simp only [blockQuadratic, pow_two, Finset.sum_mul, Finset.mul_sum, one_mul]
  exact Finset.sum_comm

theorem gaussianRadialFluctuation_second_moment :
    ∫ x, (gaussianRadialFluctuation I x)^2 ∂pairedGaussian I =
      (Fintype.card I : ℝ)⁻¹ := by
  simp_rw [gaussianRadialFluctuation_eq_block, mul_pow]
  rw [integral_const_mul]
  rw [(blockCoordinates_preserving I).integral_comp'
    (fun z : I → ℝ × ℝ => (∑ i, radialPairOutcome (z i))^2)]
  simp_rw [block_sum_square]
  erw [blockQuadratic_mean (fun _ _ : I => 1)]
  simp only [Matrix.trace, Matrix.diag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hD : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem gaussianRadialFluctuation_eLpNorm_two :
    eLpNorm (gaussianRadialFluctuation I) 2 (pairedGaussian I) =
      ENNReal.ofReal (Real.sqrt ((Fintype.card I : ℝ)⁻¹)) := by
  have hf : MemLp (gaussianRadialFluctuation I) 2 (pairedGaussian I) := by
    simpa only [ENNReal.ofReal_ofNat] using gaussianRadialFluctuation_memLp I 2 (by norm_num)
  apply (ENNReal.toReal_eq_toReal_iff' hf.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  apply (sq_eq_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).mp
  rw [eLpNorm_two_toReal_sq hf, gaussianRadialFluctuation_second_moment,
    Real.sq_sqrt (by positivity)]

theorem gaussianRadialFluctuation_abs_tail (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht : 0 < t) :
    (pairedGaussian I) {x | t ≤ |gaussianRadialFluctuation I x|} ≤
      ENNReal.ofReal ((5*(p-1)^2 * Real.sqrt ((Fintype.card I : ℝ)⁻¹) / t)^p) := by
  have hLp := paired_quartic_eLpNorm I (radialPolynomial I)
    ((radialPolynomial_degree I).trans (by decide)) p hp
  simp only [radialPolynomial_eval_fluctuation] at hLp
  rw [gaussianRadialFluctuation_eLpNorm_two, ← ENNReal.ofReal_mul (by positivity)] at hLp
  exact measure_abs_ge_le_of_eLpNorm_le _ _ (by linarith) (by positivity) ht hLp

/-- One common radial event, with the same p=n² choice as the quartic step. -/
theorem qudit_common_radius_tail {d n : Nat} (hd : 2 ≤ d) (hn : 2 ≤ n) :
    (pairedGaussian (QuditIndex d n)) {x | ((n:ℝ)^2)⁻¹ ≤ |gaussianRadius (QuditIndex d n) x - 1|} ≤
      ENNReal.ofReal ((5*((n:ℝ)^2-1)^2 * Real.sqrt ((d^n : ℝ)⁻¹) /
        ((n:ℝ)^2)⁻¹)^((n:ℝ)^2)) := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  simpa only [gaussianRadialFluctuation, qudit_card, Nat.cast_pow] using
    gaussianRadialFluctuation_abs_tail (QuditIndex d n) ((n:ℝ)^2) (by nlinarith)
      (((n:ℝ)^2)⁻¹) (by positivity)

end CertificationGaussian
