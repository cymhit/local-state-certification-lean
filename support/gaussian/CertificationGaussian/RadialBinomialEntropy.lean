import CertificationGaussian.RadialLinearCardinality
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace CertificationGaussian

theorem choose_le_exp_binEntropy (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    (n.choose k : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / n)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hkn : k = n
  · subst k
    simp [div_self hnR.ne']
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hklt : k < n := lt_of_le_of_ne hk hkn
  let p : ℝ := (k : ℝ) / n
  have hp : 0 < p := div_pos (Nat.cast_pos.mpr hkpos) hnR
  have hp1 : p < 1 := (div_lt_one hnR).mpr (by exact_mod_cast hklt)
  have hc : 0 < 1 - p := by linarith
  have hsum : (∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)) = 1 := by
    calc
      _ = (p + (1 - p)) ^ n := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 1 := by simp
  have hterm : (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ 1 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
        exact Finset.single_le_sum
          (f := fun j : ℕ => (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j))
          (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
      _ = 1 := hsum
  have hpPow : p ^ k = Real.exp ((k : ℝ) * Real.log p) := by
    rw [Real.exp_nat_mul, Real.exp_log hp]
  have hcPow : (1 - p) ^ (n - k) =
      Real.exp (((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
    rw [Real.exp_nat_mul, Real.exp_log hc]
  have hexponent : (n : ℝ) * Real.binEntropy p + (k : ℝ) * Real.log p +
      ((n - k : ℕ) : ℝ) * Real.log (1 - p) = 0 := by
    rw [Nat.cast_sub hk, Real.binEntropy, Real.log_inv, Real.log_inv]
    dsimp [p]
    field_simp
    ring
  have heq : Real.exp ((n : ℝ) * Real.binEntropy p) *
      (p ^ k * (1 - p) ^ (n - k)) = 1 := by
    rw [hpPow, hcPow, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    linarith [hexponent]
  apply (mul_le_mul_iff_left₀ (mul_pos (pow_pos hp k) (pow_pos hc (n - k)))).mp
  calc
    _ ≤ 1 := by simpa only [mul_assoc] using hterm
    _ = _ := heq.symm

/-- The displayed derivative in the paper, for an arbitrary alphabet weight M. -/
theorem hasDerivAt_weightedEntropy (M x : ℝ) (hM : 0 < M)
    (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t : ℝ => Real.binEntropy t + t * Real.log M)
      (Real.log ((1 - x) * M / x)) x := by
  have h := (Real.hasDerivAt_binEntropy hx.ne' (ne_of_lt hx1)).add
    ((hasDerivAt_id x).mul_const (Real.log M))
  have heq : Real.log ((1 - x) * M / x) =
      Real.log (1 - x) - Real.log x + 1 * Real.log M := by
    rw [Real.log_div (mul_ne_zero (by linarith) hM.ne') hx.ne',
      Real.log_mul (by linarith) hM.ne']
    ring
  rw [heq]
  exact h

/-- Strict derivative positivity gives monotonicity on the closed interval, including zero. -/
theorem weightedEntropy_strictMonoOn (M ε : ℝ) (hM : 1 ≤ M)
    (hε : 0 < ε) (hhalf : ε < 1 / 2) :
    StrictMonoOn (fun x : ℝ => Real.binEntropy x + x * Real.log M) (Icc 0 ε) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 ε)
  · fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hx.1
    have hxhalf : x < 1 / 2 := hx.2.trans hhalf
    rw [(hasDerivAt_weightedEntropy M x (by linarith) hx0 (by linarith)).deriv]
    apply Real.log_pos
    apply (lt_div_iff₀ hx0).mpr
    have h := mul_le_mul_of_nonneg_left hM (show 0 ≤ 1 - x by linarith)
    nlinarith

/-- The paper's term-by-term binomial entropy argument, retaining its (n+1) prefactor. -/
theorem weighted_binomial_floor_entropy_bound_termwise (n : ℕ) (M ε : ℝ)
    (hM : 1 ≤ M) (hε : 0 < ε) (hhalf : ε < 1 / 2) :
    (∑ k ∈ Finset.range (Nat.floor (ε * n) + 1), (n.choose k : ℝ) * M ^ k) ≤
      ((n : ℝ) + 1) * Real.exp ((n : ℝ) * (Real.binEntropy ε + ε * Real.log M)) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hM0 : 0 < M := by linarith
  have hL : Nat.floor (ε * n) ≤ n := Nat.floor_le_of_le (by nlinarith)
  have hfloor : (Nat.floor (ε * n) : ℝ) ≤ ε * n := Nat.floor_le (by positivity)
  have hmono := (weightedEntropy_strictMonoOn M ε hM hε hhalf).monotoneOn
  have hterm (k : ℕ) (hk : k ∈ Finset.range (Nat.floor (ε * n) + 1)) :
      (n.choose k : ℝ) * M ^ k ≤
        Real.exp ((n : ℝ) * (Real.binEntropy ε + ε * Real.log M)) := by
    have hkL : k ≤ Nat.floor (ε * n) := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hkn : k ≤ n := hkL.trans hL
    have hkε : (k : ℝ) / n ≤ ε := (div_le_iff₀ hnR).mpr
      ((by exact_mod_cast hkL : (k : ℝ) ≤ Nat.floor (ε * n)).trans hfloor)
    have hx : (k : ℝ) / n ∈ Icc (0 : ℝ) ε := ⟨by positivity, hkε⟩
    calc
      _ ≤ Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / n)) * M ^ k :=
        mul_le_mul_of_nonneg_right (choose_le_exp_binEntropy n k hnpos hkn) (by positivity)
      _ = Real.exp ((n : ℝ) * (Real.binEntropy ((k : ℝ) / n) +
          ((k : ℝ) / n) * Real.log M)) := by
        have hpow : M ^ k = Real.exp ((k : ℝ) * Real.log M) := by
          rw [Real.exp_nat_mul, Real.exp_log hM0]
        rw [hpow, ← Real.exp_add]
        congr 1
        field_simp
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (hmono hx ⟨hε.le, le_rfl⟩ hkε) hnR.le)
  calc
    _ ≤ ∑ _k ∈ Finset.range (Nat.floor (ε * n) + 1),
        Real.exp ((n : ℝ) * (Real.binEntropy ε + ε * Real.log M)) :=
      Finset.sum_le_sum hterm
    _ = ((Nat.floor (ε * n) : ℝ) + 1) *
        Real.exp ((n : ℝ) * (Real.binEntropy ε + ε * Real.log M)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hL)
      (Real.exp_nonneg _)

theorem radialLinearLowLabels_card_le_entropy_via_binomial_entropy (d n : ℕ) (hd : 2 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hhalf : ε < 1 / 2)
    {K : Type*} [Fintype K] [DecidableEq K] (k0 : K) (hcard : Fintype.card K = d ^ 2) :
    ((radialLinearLowLabels ε n k0).card : ℝ) ≤
      ((n : ℝ) + 1) * Real.exp ((n : ℝ) * radialLinearEntropy d ε) := by
  have hd1 : 1 ≤ d ^ 2 := by nlinarith
  have hM : (1 : ℝ) ≤ (d : ℝ) ^ 2 - 1 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hcast : ((Fintype.card K - 1 : ℕ) : ℝ) = (d : ℝ) ^ 2 - 1 := by
    rw [hcard, Nat.cast_sub hd1, Nat.cast_pow, Nat.cast_one]
  rw [radialLinearLowLabels_card]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, hcast, radialLinearWeightCutoff]
  exact weighted_binomial_floor_entropy_bound_termwise n ((d : ℝ) ^ 2 - 1) ε hM hε hhalf

/-- Absorb the paper's polynomial prefactor after termwise entropy counting. -/
theorem radialLinearLowLabels_polynomial_ratio_via_binomial_entropy (d : ℕ) (hd : 2 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hhalf : ε < 1 / 2)
    {K : Type*} [Fintype K] [DecidableEq K] (k0 : K) (hcard : Fintype.card K = d ^ 2)
    (C : ℝ) (k b : ℕ) (hgap : (b : ℝ) * radialLinearEntropy d ε < Real.log (d : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ k * ((radialLinearLowLabels ε n k0).card : ℝ) ^ b / (d : ℝ) ^ n ≤
        Real.exp (-((Real.log (d : ℝ) - (b : ℝ) * radialLinearEntropy d ε) / 2) * n) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hg : 0 < (Real.log (d : ℝ) - (b : ℝ) * radialLinearEntropy d ε) / 2 := by linarith
  by_cases hC : 0 ≤ C
  · filter_upwards [eventually_polynomial_le_exp (C * (2 : ℝ) ^ b) (k + b) hg,
      eventually_ge_atTop 1] with n hp hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpol : C * (n : ℝ) ^ k * ((n : ℝ) + 1) ^ b ≤
        (C * (2 : ℝ) ^ b) * (n : ℝ) ^ (k + b) := by
      calc
        _ ≤ C * (n : ℝ) ^ k * (2 * n) ^ b :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) b)
            (by positivity)
        _ = _ := by rw [mul_pow, pow_add]; ring
    have hpol' := hpol.trans hp
    have hm := radialLinearLowLabels_card_le_entropy_via_binomial_entropy d n hd ε hε hhalf k0 hcard
    have hpow : ((radialLinearLowLabels ε n k0).card : ℝ) ^ b ≤
        ((n : ℝ) + 1) ^ b * Real.exp ((b : ℝ) * ((n : ℝ) * radialLinearEntropy d ε)) := by
      simpa only [mul_pow, Real.exp_nat_mul] using
        pow_le_pow_left₀ (Nat.cast_nonneg _) hm b
    have hD : (d : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log (d : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hd0]
    calc
      _ ≤ (C * (n : ℝ) ^ k * (((n : ℝ) + 1) ^ b *
          Real.exp ((b : ℝ) * ((n : ℝ) * radialLinearEntropy d ε)))) / (d : ℝ) ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
      _ = (C * (n : ℝ) ^ k * ((n : ℝ) + 1) ^ b) *
          Real.exp ((b : ℝ) * ((n : ℝ) * radialLinearEntropy d ε)) / (d : ℝ) ^ n := by ring
      _ ≤ (Real.exp (((Real.log (d : ℝ) - (b : ℝ) * radialLinearEntropy d ε) / 2) * n) *
          Real.exp ((b : ℝ) * ((n : ℝ) * radialLinearEntropy d ε))) / (d : ℝ) ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpol' (Real.exp_nonneg _)) (by positivity)
      _ = _ := by rw [hD, ← Real.exp_add, ← Real.exp_sub]; congr 1; ring
  · apply Filter.Eventually.of_forall
    intro n
    have hzero : C * (n : ℝ) ^ k * ((radialLinearLowLabels ε n k0).card : ℝ) ^ b /
        (d : ℝ) ^ n ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) (by positivity)) (by positivity)) (by positivity)
    exact hzero.trans (Real.exp_nonneg _)

theorem exists_radialLinearLowLabels_exponential_via_binomial_entropy (d : ℕ) (hd : 2 ≤ d)
    {K : Type*} [Fintype K] [DecidableEq K] (k0 : K) (hcard : Fintype.card K = d ^ 2) :
    ∃ ε c : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ radialLinearEntropy d ε < Real.log (d : ℝ) / 2 ∧
      0 < c ∧ ∀ C : ℝ, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ k * ((radialLinearLowLabels ε n k0).card : ℝ) ^ 2 / (d : ℝ) ^ n ≤
        Real.exp (-c * n) := by
  obtain ⟨ε, hε, hhalf, hgap⟩ := exists_radialLinearEntropy_gap d hd
  refine ⟨ε, (Real.log (d : ℝ) - 2 * radialLinearEntropy d ε) / 2,
    hε, hhalf, hgap, by linarith, ?_⟩
  intro C k
  exact radialLinearLowLabels_polynomial_ratio_via_binomial_entropy d hd ε hε hhalf k0 hcard C k 2
    (by norm_num; linarith)

end CertificationGaussian
