import CertificationGaussian.TensorUnitaryNet
import CertificationGaussian.TailAsymptotics

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace CertificationGaussian

theorem kernelWeightL1_pos (J : Finset Nat) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    0 < kernelWeightL1 J θ := by
  have h := Finset.abs_sum_le_sum_abs θ J
  rw [hθ, abs_one] at h
  exact zero_lt_one.trans_le h

/-- A finer mesh compensates for the elementary n*D*epsilon tensor operator estimate. -/
def kernelNetMesh (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ) : ℝ :=
  Real.sqrt (kernelVarianceScale d n J θ) /
    (2*kernelWeightL1 J θ*(n:ℝ)^2*((d:ℝ)^n)^2)

theorem kernelNetMesh_pos {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    0 < kernelNetMesh d n J θ := by
  have hv := kernelVarianceScale_pos hd J hJ θ hθ
  have hL := kernelWeightL1_pos J θ hθ
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  unfold kernelNetMesh
  positivity

/-- The reciprocal mesh grows by only a fixed power of n times D². -/
theorem kernelNetMesh_inverse_le {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) (hn : max 1 (2*J.sup id) ≤ n) :
    1 / kernelNetMesh d n J θ ≤
      (2*kernelWeightL1 J θ / Real.sqrt (kernelOrderLowerConstant d J θ hθ)) *
        (n:ℝ)^(effectiveKernelOrder J θ hθ+2) * ((d:ℝ)^n)^2 := by
  have hc := kernelOrderLowerConstant_pos hd J θ hθ
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hv := (kernelVarianceScale_order_bounds hd J θ hθ hn).1
  have hL := kernelWeightL1_nonneg J θ
  have h := reciprocal_sqrt_le_of_power_lower hc hnR hv
  calc
    _ = (2*kernelWeightL1 J θ*(n:ℝ)^2*((d:ℝ)^n)^2) *
        (1/Real.sqrt (kernelVarianceScale d n J θ)) := by unfold kernelNetMesh; field_simp
    _ ≤ (2*kernelWeightL1 J θ*(n:ℝ)^2*((d:ℝ)^n)^2) *
        ((n:ℝ)^(effectiveKernelOrder J θ hθ)/Real.sqrt (kernelOrderLowerConstant d J θ hθ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The explicit local-net cardinality base is eventually at most a linear exponential. -/
theorem kernelNetMesh_base_eventually {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : Nat in atTop,
      2+4*d/kernelNetMesh d n J θ ≤ Real.exp ((1+2*Real.log d)*n) := by
  let s := effectiveKernelOrder J θ hθ
  let A := 2*kernelWeightL1 J θ/Real.sqrt (kernelOrderLowerConstant d J θ hθ)
  let C := 2+4*d*A
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast (show 1≤d by omega)
  have hd0 : (0:ℝ) < d := by linarith
  filter_upwards [eventually_polynomial_le_exp C (s+2) (show (0:ℝ)<1 by norm_num),
    eventually_ge_atTop (max 1 (2*J.sup id))] with n hpoly hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast ((le_max_left _ _).trans hn : 1≤n)
  have hi := kernelNetMesh_inverse_le hd J θ hθ hn
  have hnp : 1 ≤ (n:ℝ)^(s+2) := one_le_pow₀ hnR
  have hDp : 1 ≤ ((d:ℝ)^n)^2 := one_le_pow₀ (one_le_pow₀ hdR)
  have hp : 1 ≤ (n:ℝ)^(s+2)*((d:ℝ)^n)^2 := one_le_mul_of_one_le_of_one_le hnp hDp
  calc
    _ ≤ 2+4*d*(A*(n:ℝ)^(s+2)*((d:ℝ)^n)^2) := by
      rw [div_eq_mul_one_div]
      gcongr
    _ ≤ 2*((n:ℝ)^(s+2)*((d:ℝ)^n)^2)+4*d*(A*(n:ℝ)^(s+2)*((d:ℝ)^n)^2) := by
      gcongr
      linarith only [hp]
    _ = C*(n:ℝ)^(s+2)*((d:ℝ)^n)^2 := by dsimp [C]; ring
    _ ≤ Real.exp (1*n)*((d:ℝ)^n)^2 := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by
      have he : (d:ℝ)^n = Real.exp ((n:ℝ)*Real.log d) := by rw [Real.exp_nat_mul, Real.exp_log hd0]
      rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
      ring

theorem kernelNetMesh_eventually_pos {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : Nat in atTop, 0 < kernelNetMesh d n J θ := by
  filter_upwards [eventually_ge_atTop (max 1 (2*J.sup id))] with n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  apply kernelNetMesh_pos hd hn1 J _ θ hθ
  intro k hk
  have hk' : k ≤ J.sup id := Finset.le_sup (f := id) hk
  have ht := (le_max_right 1 (2*J.sup id)).trans hn
  omega

/-- The exact finer mesh also accommodates the coarser score Lipschitz constant 2*L*D. -/
theorem kernelNetMesh_transfer_scale {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    (2*kernelWeightL1 J θ*(d:ℝ)^n) * ((n:ℝ)*(d:ℝ)^n*kernelNetMesh d n J θ) =
      Real.sqrt (kernelVarianceScale d n J θ) / n := by
  have hL := kernelWeightL1_pos J θ hθ
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0<d by omega)
  unfold kernelNetMesh
  field_simp

/-- The explicitly constructed product net has quadratic logarithmic cardinality. -/
theorem kernelProductNet_eventually_card {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∀ᶠ n : Nat in atTop, ∀ hε : 0 < kernelNetMesh d n J θ,
      ((productUnitaryMatrixNet d n (by omega) (kernelNetMesh d n J θ) hε).card:ℝ) ≤
      Real.exp ((2*(d:ℝ)^2*(1+2*Real.log d))*(n:ℝ)^2) := by
  filter_upwards [kernelNetMesh_base_eventually hd J θ hθ] with n hn
  intro hε
  calc
    _ ≤ (2+4*d/kernelNetMesh d n J θ)^(2*d^2*n) := productUnitaryMatrixNet_card (by omega) hε
    _ ≤ (Real.exp ((1+2*Real.log d)*n))^(2*d^2*n) := pow_le_pow_left₀ (by positivity) hn _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- An actual net, its quantitative cover and cardinality, and its cubic Gaussian bad-event bound. -/
theorem actual_kernel_net_cubic {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : Nat, ∀ n ≥ N,
      0 < kernelNetMesh d n J θ ∧
      ∃ S : Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ),
        (∀ W ∈ S, W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) ∧
        (S.card:ℝ) ≤ Real.exp (K*(n:ℝ)^2) ∧
        (∀ U : Fin n → LocalUnitary d, ∃ W ∈ S,
          ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ) (tensorUnitaryMatrix d n U-W)‖ ≤
            n*(d:ℝ)^n*kernelNetMesh d n J θ) ∧
        (pairedGaussian (QuditIndex d n))
          {x | ∃ W ∈ S, kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ W x|} ≤
        ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := by
  let K := 2*(d:ℝ)^2*(1+2*Real.log d)
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  have hlog := Real.log_pos hdR
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, Filter.eventually_atTop.mp ?_⟩
  filter_upwards [kernelNetMesh_eventually_pos hd J θ hθ,
    kernelProductNet_eventually_card hd J θ hθ,
    quditQuartic_eventually_finite_family_cubic hd J θ hθ K] with n hε hcard hprob
  let S := productUnitaryMatrixNet d n (by omega) (kernelNetMesh d n J θ) hε
  have hS : ∀ W ∈ S, W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) :=
    fun _ hW => productUnitaryMatrixNet_unitary (by omega) hε hW
  refine ⟨hε, S, hS, hcard hε, ?_, hprob S hS (hcard hε)⟩
  exact productUnitaryMatrixNet_covers (by omega) hε

end CertificationGaussian
