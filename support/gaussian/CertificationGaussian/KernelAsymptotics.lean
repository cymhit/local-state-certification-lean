import CertificationGaussian.KernelOperator
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Max

noncomputable section
open scoped BigOperators
namespace CertificationGaussian

/-- The effective support excludes zero coefficients; J itself need not have full support. -/
def effectiveKernelSupport (J : Finset Nat) (θ : Nat → ℝ) : Finset Nat := by
  classical
  exact J.filter (fun k => θ k ≠ 0)

theorem effectiveKernelSupport_nonempty (J : Finset Nat) (θ : Nat → ℝ)
    (hθ : ∑ k ∈ J, θ k = 1) : (effectiveKernelSupport J θ).Nonempty := by
  classical
  by_contra h
  have hz : ∀ k ∈ J, θ k = 0 := by
    intro k hk
    by_contra hk0
    exact h ⟨k, by simp [effectiveKernelSupport, hk, hk0]⟩
  have hs := Finset.sum_eq_zero hz
  rw [hθ] at hs
  norm_num at hs

def effectiveKernelOrder (J : Finset Nat) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) : Nat :=
  (effectiveKernelSupport J θ).min' (effectiveKernelSupport_nonempty J θ hθ)

theorem effectiveKernelOrder_mem (J : Finset Nat) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    effectiveKernelOrder J θ hθ ∈ J ∧ θ (effectiveKernelOrder J θ hθ) ≠ 0 := by
  classical
  have h := Finset.min'_mem (effectiveKernelSupport J θ) (effectiveKernelSupport_nonempty J θ hθ)
  simpa only [effectiveKernelOrder, effectiveKernelSupport, Finset.mem_filter] using h

theorem effectiveKernelOrder_le (J : Finset Nat) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1)
    {k : Nat} (hk : k ∈ J) (hk0 : θ k ≠ 0) : effectiveKernelOrder J θ hθ ≤ k := by
  classical
  apply Finset.min'_le
  simp [effectiveKernelSupport, hk, hk0]

theorem effectiveKernelOrder_pos (J : Finset Nat) (hJ : ∀ k ∈ J, 1 ≤ k)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) : 1 ≤ effectiveKernelOrder J θ hθ :=
  hJ _ (effectiveKernelOrder_mem J θ hθ).1

/-- A direct finite-n lower bound; no asymptotic approximation of choose is assumed. -/
theorem choose_lower_half {n k : Nat} (hk : 2*k ≤ n) :
    (n:ℝ)^k / ((2:ℝ)^k * (k.factorial:ℝ)) ≤ (Nat.choose n k : ℝ) := by
  have hNat : n ≤ 2*(n+1-k) := by omega
  have hcast : (n:ℝ) ≤ 2 * ((n+1-k:Nat):ℝ) := by exact_mod_cast hNat
  have hhalf : (n:ℝ)/2 ≤ ((n+1-k:Nat):ℝ) := by linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (n:ℝ)/2) hhalf k
  have h := (div_le_div_of_nonneg_right hpow (Nat.cast_nonneg' k.factorial)).trans
    (Nat.pow_le_choose (α := ℝ) k n)
  convert h using 1
  rw [div_pow]
  ring

/-- Lower bound for one variance summand, with its exact leading coefficient. -/
theorem kernel_term_lower {d n k : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n) (hk : k ≤ n) (a : ℝ) :
    (a^2 * (k.factorial:ℝ) / ((d-1:Nat):ℝ)^k) / (n:ℝ)^k ≤
      a^2 / ((Nat.choose n k:ℝ) * ((d-1:Nat):ℝ)^k) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hb : (0:ℝ) < ((d-1:Nat):ℝ) := by exact_mod_cast (show 0<d-1 by omega)
  have hfac : (0:ℝ) < (k.factorial:ℝ) := by exact_mod_cast k.factorial_pos
  calc
    _ = a^2 / (((n:ℝ)^k / (k.factorial:ℝ)) * ((d-1:Nat):ℝ)^k) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg a) (distance_denominator_pos hd hk)
      (mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div (α := ℝ) k n) (by positivity))

/-- Upper bound for one summand once n is at least twice its shell index. -/
theorem kernel_term_upper {d n k : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n) (hk : 2*k ≤ n) (a : ℝ) :
    a^2 / ((Nat.choose n k:ℝ) * ((d-1:Nat):ℝ)^k) ≤
      (a^2 * (2:ℝ)^k * (k.factorial:ℝ) / ((d-1:Nat):ℝ)^k) / (n:ℝ)^k := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hb : (0:ℝ) < ((d-1:Nat):ℝ) := by exact_mod_cast (show 0<d-1 by omega)
  have hfac : (0:ℝ) < (k.factorial:ℝ) := by exact_mod_cast k.factorial_pos
  calc
    _ ≤ a^2 / (((n:ℝ)^k / ((2:ℝ)^k * (k.factorial:ℝ))) * ((d-1:Nat):ℝ)^k) :=
      div_le_div_of_nonneg_left (sq_nonneg a) (by positivity)
        (mul_le_mul_of_nonneg_right (choose_lower_half hk) (by positivity))
    _ = _ := by field_simp

def kernelOrderLowerConstant (d : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (hθ : ∑ k ∈ J, θ k = 1) : ℝ :=
  (θ (effectiveKernelOrder J θ hθ))^2 * ((effectiveKernelOrder J θ hθ).factorial:ℝ) /
    ((d-1:Nat):ℝ)^(effectiveKernelOrder J θ hθ)

def kernelOrderUpperConstant (d : Nat) (J : Finset Nat) (θ : Nat → ℝ) : ℝ :=
  ∑ k ∈ J, (θ k)^2 * (2:ℝ)^k * (k.factorial:ℝ) / ((d-1:Nat):ℝ)^k

theorem kernelOrderLowerConstant_pos {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) : 0 < kernelOrderLowerConstant d J θ hθ := by
  have hsq := sq_pos_of_ne_zero (effectiveKernelOrder_mem J θ hθ).2
  have hb : (0:ℝ) < ((d-1:Nat):ℝ) := by exact_mod_cast (show 0<d-1 by omega)
  unfold kernelOrderLowerConstant
  positivity

theorem kernelOrderUpperConstant_pos {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) : 0 < kernelOrderUpperConstant d J θ := by
  have hs := effectiveKernelOrder_mem J θ hθ
  have hsq := sq_pos_of_ne_zero hs.2
  have hb : (0:ℝ) < ((d-1:Nat):ℝ) := by exact_mod_cast (show 0<d-1 by omega)
  have hp : 0 < (θ (effectiveKernelOrder J θ hθ))^2 * (2:ℝ)^(effectiveKernelOrder J θ hθ) *
      ((effectiveKernelOrder J θ hθ).factorial:ℝ) / ((d-1:Nat):ℝ)^(effectiveKernelOrder J θ hθ) := by positivity
  exact hp.trans_le (Finset.single_le_sum
    (f := fun k => (θ k)^2 * (2:ℝ)^k * (k.factorial:ℝ) / ((d-1:Nat):ℝ)^k)
    (fun _ _ => by positivity) hs.1)

/-- Uniform explicit two-sided order bounds from the effective nonzero support. -/
theorem kernelVarianceScale_order_bounds {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1)
    (hn : max 1 (2 * J.sup id) ≤ n) :
    kernelOrderLowerConstant d J θ hθ / (n:ℝ)^(effectiveKernelOrder J θ hθ) ≤
      kernelVarianceScale d n J θ ∧
    kernelVarianceScale d n J θ ≤
      kernelOrderUpperConstant d J θ / (n:ℝ)^(effectiveKernelOrder J θ hθ) := by
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hkn {k : Nat} (hk : k ∈ J) : 2*k ≤ n := by
    have hsup : k ≤ J.sup id := Finset.le_sup (f := id) hk
    have hm := le_trans (le_max_right 1 (2*J.sup id)) hn
    omega
  constructor
  · have hs := (effectiveKernelOrder_mem J θ hθ).1
    have hsn := hkn hs
    exact (kernel_term_lower hd hn1 (by omega) (θ (effectiveKernelOrder J θ hθ))).trans
      (Finset.single_le_sum (f := fun k => (θ k)^2 /
        ((Nat.choose n k:ℝ) * ((d-1:Nat):ℝ)^k)) (fun _ _ => by positivity) hs)
  · unfold kernelVarianceScale kernelOrderUpperConstant
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hk0 : θ k = 0
    · simp [hk0]
    · have hmin := effectiveKernelOrder_le J θ hθ hk hk0
      have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
      exact (kernel_term_upper hd hn1 (hkn hk) (θ k)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_right₀ hnR hmin))

/-- An explicit eventual Theta statement, retaining positive lower and upper constants. -/
theorem kernelVarianceScale_two_sided_power_order {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : Nat, ∀ n ≥ N,
      c / (n:ℝ)^(effectiveKernelOrder J θ hθ) ≤ kernelVarianceScale d n J θ ∧
      kernelVarianceScale d n J θ ≤ C / (n:ℝ)^(effectiveKernelOrder J θ hθ) := by
  exact ⟨kernelOrderLowerConstant d J θ hθ, kernelOrderUpperConstant d J θ,
    kernelOrderLowerConstant_pos hd J θ hθ, kernelOrderUpperConstant_pos hd J θ hθ,
    max 1 (2 * J.sup id), fun n hn => kernelVarianceScale_order_bounds hd J θ hθ hn⟩

end CertificationGaussian
