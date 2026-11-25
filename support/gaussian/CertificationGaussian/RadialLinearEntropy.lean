import CertificationGaussian.RadialLowCardinality
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
open Filter
open scoped BigOperators Topology
namespace CertificationGaussian

/-- The entropy exponent for the local Weyl alphabet of cardinality d². -/
def radialLinearEntropy (d : ℕ) (ε : ℝ) : ℝ :=
  Real.binEntropy ε+ε*Real.log ((d:ℝ)^2-1)

/-- A strictly positive fixed linear cutoff can satisfy the original strict entropy gap. -/
theorem exists_radialLinearEntropy_gap (d : ℕ) (hd : 2≤d) :
    ∃ ε : ℝ,0<ε ∧ ε<1/2 ∧ radialLinearEntropy d ε<Real.log (d:ℝ)/2 := by
  have hl : 0<Real.log (d:ℝ)/2 := by
    have h := Real.log_pos (show (1:ℝ)<d by exact_mod_cast (show 1<d by omega))
    positivity
  have hc : Continuous (radialLinearEntropy d) := by unfold radialLinearEntropy; fun_prop
  obtain ⟨δ,hδ,hsmall⟩ := Metric.continuousAt_iff.mp hc.continuousAt (Real.log (d:ℝ)/2) hl
  let ε : ℝ := min (δ/2) (1/4)
  have hε : 0<ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε<δ := (min_le_left _ _).trans_lt (by linarith)
  have hehalf : ε<1/2 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨ε,hε,hehalf,?_⟩
  have h := hsmall (show dist ε 0<δ by simpa only [Real.dist_eq,sub_zero,abs_of_pos hε] using hεδ)
  simp only [radialLinearEntropy,Real.binEntropy_zero,zero_mul,add_zero,Real.dist_eq,sub_zero] at h
  exact (le_abs_self _).trans_lt h

/-- Finite generating-function estimate for the actual weighted binomial partial sum.
It is valid at n=0, and uses no asymptotic or entropy hypothesis. -/
theorem weighted_binomial_partial_bound (n L : ℕ) (hL : L≤n) (M t : ℝ)
    (hM : 0≤M) (ht0 : 0<t) (ht1 : t≤1) :
    (∑ k∈Finset.range (L+1),(n.choose k:ℝ)*M^k)≤(1+M*t)^n/t^L := by
  apply (le_div_iff₀ (pow_pos ht0 L)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ k∈Finset.range (L+1),(n.choose k:ℝ)*M^k*t^k := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0.le ht1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _))
    _ ≤ ∑ k∈Finset.range (n+1),(n.choose k:ℝ)*M^k*t^k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro k _ _
      positivity
    _ = (1+M*t)^n := by
      rw [add_comm 1,add_pow]
      apply Finset.sum_congr rfl
      intro k _
      simp only [one_pow,mul_one,mul_pow]
      ring

/-- A finite weighted binomial ball with floor(epsilon*n) radius satisfies the exact entropy bound.
This generating-function proof is stronger than the paper's harmless polynomial prefactor. -/
theorem weighted_binomial_floor_entropy_bound (n : ℕ) (M ε : ℝ)
    (hM : 1≤M) (hε : 0<ε) (hεhalf : ε<1/2) :
    (∑ k∈Finset.range (Nat.floor (ε*n)+1),(n.choose k:ℝ)*M^k)≤
      Real.exp ((n:ℝ)*(Real.binEntropy ε+ε*Real.log M)) := by
  have hM0 : 0<M := by linarith
  have hε1 : ε<1 := by linarith
  have hcomp : 0<1-ε := by linarith
  let t : ℝ := ε/(M*(1-ε))
  have ht0 : 0<t := by dsimp [t]; positivity
  have ht1 : t<1 := by
    apply (div_lt_one (mul_pos hM0 hcomp)).mpr
    have hm := mul_le_mul_of_nonneg_right hM hcomp.le
    nlinarith
  have hL : Nat.floor (ε*n)≤n := Nat.floor_le_of_le (by nlinarith [Nat.cast_nonneg (α:=ℝ) n])
  have hf : (Nat.floor (ε*n):ℝ)≤ε*n := Nat.floor_le (by positivity)
  have hb : 0<1+M*t := by positivity
  have hbase : 1+M*t=(1-ε)⁻¹ := by dsimp [t]; field_simp; ring
  have hlog : Real.log t=Real.log ε-Real.log M-Real.log (1-ε) := by
    dsimp [t]
    rw [Real.log_div hε.ne' (mul_pos hM0 hcomp).ne',Real.log_mul hM0.ne' hcomp.ne']
    ring
  have hent : Real.log (1+M*t)-ε*Real.log t=Real.binEntropy ε+ε*Real.log M := by
    rw [hbase,Real.log_inv,hlog,Real.binEntropy,Real.log_inv,Real.log_inv]
    ring
  have hex : (1+M*t)^n/t^(Nat.floor (ε*n))=
      Real.exp ((n:ℝ)*Real.log (1+M*t)-(Nat.floor (ε*n):ℝ)*Real.log t) := by
    rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log hb,Real.exp_log ht0]
  refine (weighted_binomial_partial_bound n (Nat.floor (ε*n)) hL M t hM0.le ht0 ht1.le).trans ?_
  rw [hex]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (n:ℝ)*Real.log (1+M*t)-(ε*n)*Real.log t := by
      linarith [mul_le_mul_of_nonpos_right hf (Real.log_neg ht0 ht1).le]
    _ = (n:ℝ)*(Real.log (1+M*t)-ε*Real.log t) := by ring
    _ = _ := by rw [hent]

end CertificationGaussian
