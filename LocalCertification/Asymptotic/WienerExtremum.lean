import LocalCertification.Asymptotic.WienerSeries

/-! # Real and complex repeated-node Wiener extrema -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial
noncomputable section
namespace LocalCertification.Asymptotic.Wiener

def positiveNorm (c : ℕ → ℂ) : ℝ := ∑' n, ‖c (n + 1)‖

def boundaryNorm (c : ℕ → ℂ) : ℝ := positiveNorm c + ‖series c 1‖

/-- The Wiener extremum for a node of multiplicity `r+1`. -/
def phi (a : ℝ) (r : ℕ) : ℝ := sInf (positiveNorm '' {c | Feasible a r c})

def realLift (a : ℝ) (r : ℕ) (f : ℕ → ℝ) : ℕ → ℂ
  | 0 => (a : ℂ) ^ (r + 1)
  | n + 1 => (f n : ℂ)

theorem lift_feasible (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (r : ℕ)
    (f : ℕ → ℝ) (hf : MomentFeasible a r f) : Feasible a r (realLift a r f) := by
  have norm : Summable (fun n => ‖realLift a r f n‖) := by
    rw [← summable_nat_add_iff 1]
    simpa only [realLift, Complex.norm_real, Real.norm_eq_abs] using hf.1
  refine ⟨norm, rfl, (derivatives_iff_polynomial_moments a ha ha1 r _ norm).2 ?_⟩
  intro p hp
  apply (hasSum_nat_add_iff' (f := fun n : ℕ =>
    realLift a r f n * (a : ℂ)^n * Complex.ofReal (p.eval (n : ℝ))) 1).mp
  have h := Complex.ofRealCLM.hasSum (hf.2 p hp)
  simpa only [Finset.range_one, Finset.sum_singleton, realLift, pow_zero, mul_one, Nat.cast_zero,
    Nat.cast_add, Nat.cast_one, zero_sub, Complex.ofRealCLM_apply, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_natCast, neg_mul] using h

theorem lift_at_one (a : ℝ) (r : ℕ) (f : ℕ → ℝ) (hf : MomentFeasible a r f) :
    series (realLift a r f) 1 = Complex.ofReal (atOne a r f) := by
  have norm : Summable (fun n => ‖f n‖) := by simpa only [Real.norm_eq_abs] using hf.1
  have h := Complex.ofRealCLM.hasSum (norm.of_norm.hasSum : HasSum f (∑' n, f n))
  have hs : HasSum (realLift a r f) (Complex.ofReal (atOne a r f)) := by
    apply (hasSum_nat_add_iff' (f := realLift a r f) 1).mp
    simpa [realLift, atOne] using h
  simpa [series] using hs.tsum_eq

theorem real_projection (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (r : ℕ)
    (c : ℕ → ℂ) (hc : Feasible a r c) :
    let f := fun n => (c (n + 1)).re
    MomentFeasible a r f ∧ tailNorm f ≤ positiveNorm c ∧
      atOne a r f = (series c 1).re := by
  dsimp only
  have nt : Summable (fun n => ‖c (n + 1)‖) := (summable_nat_add_iff 1).mpr hc.1
  have nre : Summable (fun n => |(c (n + 1)).re|) :=
    nt.of_nonneg_of_le (fun _ => abs_nonneg _) (fun _ => Complex.abs_re_le_norm _)
  refine ⟨⟨nre, ?_⟩, nre.tsum_le_tsum (fun _ => Complex.abs_re_le_norm _) nt, ?_⟩
  · intro p hp
    have h0 := ((derivatives_iff_polynomial_moments a ha ha1 r c hc.1).1 hc.2.2 p hp)
    have h := Complex.reCLM.hasSum ((hasSum_nat_add_iff' 1).mpr h0)
    simp only [Finset.range_one, Finset.sum_singleton, hc.2.1, pow_zero, mul_one,
      Nat.cast_zero, zero_sub, map_neg, Complex.reCLM_apply, Nat.cast_add, Nat.cast_one,
      ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at h
    simpa only [neg_mul] using h
  · have cs : Summable c := hc.1.of_norm
    have h := Complex.reCLM.hasSum ((hasSum_nat_add_iff' (f := c) 1).mpr cs.hasSum)
    simp only [Finset.range_one, Finset.sum_singleton, hc.2.1, map_sub, Complex.reCLM_apply,
      ← Complex.ofReal_pow, Complex.ofReal_re] at h
    rw [atOne, h.tsum_eq, series]
    simp

private theorem positiveNorm_lift (a : ℝ) (r : ℕ) (f : ℕ → ℝ) :
    positiveNorm (realLift a r f) = tailNorm f := by
  simp only [positiveNorm, tailNorm, realLift, Complex.norm_real, Real.norm_eq_abs]

theorem phi_eq_real_moment_infimum (q : ℝ) (hq : 1 < q) (r : ℕ) :
    phi q⁻¹ r = momentInfimum q⁻¹ r := by
  have ha : 0 < q⁻¹ := inv_pos.mpr (by linarith)
  have ha1 := inv_lt_one_of_one_lt₀ hq
  obtain ⟨f, hf, _⟩ := finite_dual_attains q hq r
  have hc := lift_feasible _ ha ha1 r f hf
  have hC : BddBelow (positiveNorm '' {c | Feasible q⁻¹ r c}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, _, rfl⟩
    exact tsum_nonneg (fun _ => norm_nonneg _)
  have hR : BddBelow (tailNorm '' {f | MomentFeasible q⁻¹ r f}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, _, rfl⟩
    exact tsum_nonneg (fun _ => abs_nonneg _)
  apply le_antisymm
  · unfold momentInfimum
    apply le_csInf (s := tailNorm '' {t | MomentFeasible q⁻¹ r t}) ⟨_, f, hf, rfl⟩
    rintro _ ⟨t, ht, rfl⟩
    exact csInf_le hC ⟨realLift _ _ t, lift_feasible _ ha ha1 r t ht, positiveNorm_lift _ _ t⟩
  · unfold phi
    apply le_csInf (s := positiveNorm '' {t | Feasible q⁻¹ r t}) ⟨_, _, hc, rfl⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨hgood, hnorm, _⟩ := real_projection _ ha ha1 r t ht
    exact (csInf_le hR ⟨_, hgood, rfl⟩).trans hnorm

/-- The finite dual attains the infimum even over *all complex* feasible series. -/
theorem augmented_complex_infimum (q : ℝ) (hq : 1 < q) (r : ℕ) :
    Extremal.extremalValue q r = (q⁻¹ ^ (r + 1))⁻¹ *
      sInf (boundaryNorm '' {c | Feasible q⁻¹ r c}) := by
  have ha : 0 < q⁻¹ := inv_pos.mpr (by linarith)
  have ha1 := inv_lt_one_of_one_lt₀ hq
  let A := q⁻¹ ^ (r + 1)
  have hA : A ≠ 0 := (pow_pos ha _).ne'
  have hlow : ∀ v ∈ boundaryNorm '' {c | Feasible q⁻¹ r c},
      A * Extremal.extremalValue q r ≤ v := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hf, ht, hb⟩ := real_projection _ ha ha1 r c hc
    have h := extremal_le_augmented q hq r _ hf
    have hp := mul_le_mul_of_nonneg_left h (pow_pos ha (r+1)).le
    change A * _ ≤ A * (A⁻¹ * _) at hp
    simp only [← mul_assoc, mul_inv_cancel₀ hA, one_mul] at hp
    apply hp.trans
    unfold augmentedNorm boundaryNorm
    rw [hb]
    exact add_le_add ht (Complex.abs_re_le_norm _)
  obtain ⟨f, hf, he⟩ := finite_dual_attains q hq r
  have hm : A * Extremal.extremalValue q r ∈ boundaryNorm '' {c | Feasible q⁻¹ r c} := by
    refine ⟨realLift _ _ f, lift_feasible _ ha ha1 r f hf, ?_⟩
    simpa only [boundaryNorm, positiveNorm_lift, lift_at_one _ _ _ hf,
      Complex.norm_real, Real.norm_eq_abs, augmentedNorm, A] using he
  rw [le_antisymm (csInf_le ⟨_, hlow⟩ hm) (le_csInf ⟨_, hm⟩ hlow)]
  change _ = A⁻¹ * (A * _)
  rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]

theorem interpolation_sandwich (q : ℝ) (hq : 1 < q) (r : ℕ) :
    (q⁻¹ ^ (r + 1))⁻¹ * phi q⁻¹ r ≤ Extremal.extremalValue q r ∧
    Extremal.extremalValue q r ≤ 2 * (q⁻¹ ^ (r + 1))⁻¹ * phi q⁻¹ r + 1 := by
  rw [phi_eq_real_moment_infimum q hq r]
  exact moment_infimum_sandwich q hq r

end LocalCertification.Asymptotic.Wiener
