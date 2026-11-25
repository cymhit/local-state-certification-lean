import LocalCertification.Extremal.DimensionParameters

/-! # The qubit quadratic via its roots and extrapolation nodes -/

set_option autoImplicit false
open Polynomial
open scoped OnePoint
noncomputable section
namespace LocalCertification.Manuscript

/-- The normalized quadratic with roots 2 and 35/29. -/
def qubitQuadratic : ℝ[X] := C (1 / 70) * (X - 2) * (C 29 * X - 35)

private theorem qubitQuadratic_eval (x : ℝ) :
    qubitQuadratic.eval x = (x - 2) * (29 * x - 35) / 70 := by
  simp [qubitQuadratic]
  ring

private def rootRatio (root x : ℝ) : ℝ := (x + 1 - root) / (x - root)

private theorem rootRatio_pos {a x : ℝ} (ha : a < x) : 0 < rootRatio a x :=
  div_pos (by linarith) (sub_pos.mpr ha)

private theorem rootRatio_antitone {a x y : ℝ} (ha : a < x) (hxy : x ≤ y) :
    rootRatio a y ≤ rootRatio a x := by
  apply (div_le_div_iff₀ (sub_pos.mpr (lt_of_lt_of_le ha hxy)) (sub_pos.mpr ha)).mpr
  nlinarith

private theorem qubitQuadratic_pos {x : ℝ} (hx : 4 ≤ x) : 0 < qubitQuadratic.eval x := by
  rw [qubitQuadratic_eval]
  exact div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)

/-- Factoring the ratio at consecutive weights gives two positive decreasing factors. -/
theorem qubit_quadratic_successive_ratio (x : ℝ) (hx : 4 ≤ x) :
    qubitQuadratic.eval (x + 1) / qubitQuadratic.eval x =
      (x - 1) / (x - 2) * ((x + 1 - 35 / 29) / (x - 35 / 29)) := by
  rw [qubitQuadratic_eval, qubitQuadratic_eval]
  field_simp [show x - 2 ≠ 0 by linarith, show 29 * x - 35 ≠ 0 by linarith,
    show x - 35 / 29 ≠ 0 by linarith]
  ring

theorem qubit_quadratic_ratio_antitone :
    AntitoneOn (fun x : ℝ => qubitQuadratic.eval (x + 1) / qubitQuadratic.eval x)
      (Set.Ici 4) := by
  intro x hx y hy hxy
  change qubitQuadratic.eval (y + 1) / qubitQuadratic.eval y ≤
    qubitQuadratic.eval (x + 1) / qubitQuadratic.eval x
  rw [qubit_quadratic_successive_ratio y hy, qubit_quadratic_successive_ratio x hx]
  have h₁ := rootRatio_antitone (a := 2) (x := x) (y := y)
    (by have : 4 ≤ x := hx; linarith) hxy
  have h₂ := rootRatio_antitone (a := 35/29) (x := x) (y := y)
    (by have : 4 ≤ x := hx; linarith) hxy
  have h₃ := rootRatio_pos (a := 35/29) (x := y) (by have : 4 ≤ y := hy; linarith)
  have h₄ := rootRatio_pos (a := 2) (x := x) (by have : 4 ≤ x := hx; linarith)
  convert mul_le_mul h₁ h₂ h₃.le h₄.le using 1 <;> unfold rootRatio <;> ring

theorem qubit_quadratic_tail_step (w : ℕ) (hw : 4 ≤ w) :
    weightedSample 2 qubitQuadratic (w + 1) ≤ weightedSample 2 qubitQuadratic w := by
  have hw' : (4 : ℝ) ≤ w := by exact_mod_cast hw
  have hr := qubit_quadratic_ratio_antitone (show (4 : ℝ) ∈ Set.Ici 4 from le_refl (4 : ℝ))
    (show (w : ℝ) ∈ Set.Ici 4 from hw') hw'
  have h4 : qubitQuadratic.eval (4 + 1) / qubitQuadratic.eval 4 = 55 / 27 := by
    norm_num [qubitQuadratic_eval]
  change qubitQuadratic.eval ((w : ℝ) + 1) / qubitQuadratic.eval (w : ℝ) ≤
    qubitQuadratic.eval (4 + 1) / qubitQuadratic.eval 4 at hr
  rw [h4] at hr
  have h := (div_le_iff₀ (qubitQuadratic_pos hw')).mp (hr.trans (by norm_num : (55 : ℝ) / 27 ≤ 3))
  unfold weightedSample
  rw [pow_succ, Nat.cast_add, Nat.cast_one, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  norm_num
  linarith

/-- The full integer envelope, including the tail above the last positive contact. -/
theorem qubit_quadratic_endpoints : (ell 2 qubitQuadratic, u 2 qubitQuadratic) = (0, 1 / 35) := by
  have tail (w : ℕ) (hw : 4 ≤ w) :
      weightedSample 2 qubitQuadratic w ≤ weightedSample 2 qubitQuadratic 4 := by
    induction w, hw using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact (qubit_quadratic_tail_step k hk).trans ih
  have hs (k : ℕ) : 0 ≤ weightedSample 2 qubitQuadratic (k + 1) ∧
      weightedSample 2 qubitQuadratic (k + 1) ≤ 1 / 35 := by
    by_cases hk : 4 ≤ k + 1
    · have hw : (4 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk
      refine ⟨mul_nonneg (by positivity) (qubitQuadratic_pos hw).le, (tail _ hk).trans ?_⟩
      norm_num [weightedSample, qubitQuadratic_eval]
    · have h : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases h with rfl | rfl | rfl <;> norm_num [weightedSample, qubitQuadratic_eval]
  apply Prod.ext
  · apply le_antisymm (Extremal.envelope_zero_bounds (2 + 1) (by norm_num) _).1
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    exact (hs k).1
  · apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨k, rfl⟩
      exact (hs k).2
    · have h := Extremal.le_upperEnvelope (2 + 1) (by norm_num) qubitQuadratic 0
      change weightedSample 2 qubitQuadratic 1 ≤ u 2 qubitQuadratic at h
      simpa only [show weightedSample 2 qubitQuadratic 1 = 1/35 by
        norm_num [weightedSample, qubitQuadratic_eval]] using h

/-- The three finite samples and the value at infinity reproduce evaluation at zero. -/
theorem qubit_quadratic_extrapolation (c : Extremal.CoeffSpace 2) :
    Extremal.extrapolation 2 c =
      8 * Extremal.polynomialNode 3 c.1 (Extremal.coefficientPolynomial c) (0 : ℕ) -
      18 * Extremal.polynomialNode 3 c.1 (Extremal.coefficientPolynomial c) (1 : ℕ) +
      27 * Extremal.polynomialNode 3 c.1 (Extremal.coefficientPolynomial c) (3 : ℕ) -
      16 * Extremal.polynomialNode 3 c.1 (Extremal.coefficientPolynomial c) ∞ := by
  simp [Extremal.extrapolation_formula, Extremal.polynomialNode_nat,
    Extremal.polynomialNode_infty, Extremal.coefficientPolynomial_eval, Fin.sum_univ_succ]
  ring

theorem qubit_quadratic_exact : gamma 2 2 = 1 / 35 := by
  have hq : (1 : ℝ) < 3 := by norm_num
  apply le_antisymm
  · have hp : Extremal.admissible 2 qubitQuadratic := by
      refine ⟨?_, by norm_num [qubitQuadratic_eval]⟩
      unfold qubitQuadratic
      compute_degree
    have h := csInf_le (Extremal.envelope_ratios_bddBelow (2 + 1) (by norm_num) 2)
      ⟨qubitQuadratic, hp, rfl⟩
    have hl := congrArg Prod.fst qubit_quadratic_endpoints
    have hu := congrArg Prod.snd qubit_quadratic_endpoints
    change ell 2 qubitQuadratic = 0 at hl
    change u 2 qubitQuadratic = 1 / 35 at hu
    change gamma 2 2 ≤ (u 2 qubitQuadratic - ell 2 qubitQuadratic) / (1 - ell 2 qubitQuadratic) at h
    simpa [hl, hu] using h
  · obtain ⟨c, hc, hm⟩ := Extremal.extremalValue_attained 3 hq 2
    have h := qubit_quadratic_extrapolation c
    rw [hm] at h
    have hB : Extremal.extremalValue 3 2 ≤ 69 := by
      linarith [(abs_le.mp (hc (0 : ℕ))).2, (abs_le.mp (hc (1 : ℕ))).1,
        (abs_le.mp (hc (3 : ℕ))).2, (abs_le.mp (hc ∞)).1]
    rw [gamma, show (2 : ℝ) + 1 = 3 by norm_num, Extremal.gamma_eq_extremalValue _ hq]
    have hpos := Extremal.one_lt_extremalValue 3 hq 2
    apply (le_div_iff₀ (by linarith : 0 < 1 + Extremal.extremalValue 3 2)).mpr
    linarith

end LocalCertification.Manuscript
