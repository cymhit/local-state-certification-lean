import CertificationGaussian.RadialLinearEntropy
import CertificationGaussian.RadialLowAsymptotics

noncomputable section
open Filter
open scoped BigOperators Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The linear weight cutoff used in the exponential typicality bound. -/
def radialLinearWeightCutoff (ε : ℝ) (n : ℕ) : ℕ := Nat.floor (ε*n)

/-- Original nonidentity-support words at or below the fixed linear cutoff. -/
def radialLinearLowLabels (ε : ℝ) (n : ℕ) (k0 : K) : Finset (Fin n → K) :=
  Finset.univ.filter (fun w => (radialBellSupport k0 w).card≤radialLinearWeightCutoff ε n)

/-- Exact actual shell count at the linear cutoff, including n=0 and cutoffs exceeding n. -/
theorem radialLinearLowLabels_card (ε : ℝ) (n : ℕ) (k0 : K) :
    (radialLinearLowLabels ε n k0).card=
      ∑ j∈Finset.range (radialLinearWeightCutoff ε n+1),n.choose j*(Fintype.card K-1)^j := by
  have h := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (Fin n → K))
    (Finset.range (radialLinearWeightCutoff ε n+1)) (fun w => (radialBellSupport k0 w).card) (fun _ => (1:ℕ))
  simp only [Finset.sum_const,smul_eq_mul,mul_one,Finset.mem_range,Nat.lt_succ_iff] at h
  calc
    _ = ∑ j∈Finset.range (radialLinearWeightCutoff ε n+1),
        (Finset.univ.filter (fun w : Fin n → K => (radialBellSupport k0 w).card=j)).card := by
      simpa only [radialLinearLowLabels] using h.symm
    _ = _ := by simp_rw [radialBellSupport_shell_card]

/-- The actual d-squared Weyl-label ball satisfies the exact original entropy exponent. -/
theorem radialLinearLowLabels_card_le_entropy (d n : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hεhalf : ε<1/2) (k0 : K) (hcard : Fintype.card K=d^2) :
    ((radialLinearLowLabels ε n k0).card:ℝ)≤Real.exp ((n:ℝ)*radialLinearEntropy d ε) := by
  have hd1 : 1≤d^2 := by nlinarith
  have hM : (1:ℝ)≤(d:ℝ)^2-1 := by
    have h : (2:ℝ)≤d := by exact_mod_cast hd
    nlinarith
  have hcast : ((Fintype.card K-1:ℕ):ℝ)=(d:ℝ)^2-1 := by
    rw [hcard,Nat.cast_sub hd1,Nat.cast_pow,Nat.cast_one]
  have hc : ((radialLinearLowLabels ε n k0).card:ℝ)=
      ∑ j∈Finset.range (Nat.floor (ε*n)+1),(n.choose j:ℝ)*((d:ℝ)^2-1)^j := by
    rw [radialLinearLowLabels_card]
    simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,hcast,radialLinearWeightCutoff]
  rw [hc]
  exact weighted_binomial_floor_entropy_bound n ((d:ℝ)^2-1) ε hM hε hεhalf

/-- The actual count divided by dimension, to any fixed power b satisfying the entropy gap, is exponentially small. -/
theorem radialLinearLowLabels_polynomial_ratio (d : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hεhalf : ε<1/2) (k0 : K) (hcard : Fintype.card K=d^2)
    (C : ℝ) (k b : ℕ) (hgap : (b:ℝ)*radialLinearEntropy d ε<Real.log (d:ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      C*(n:ℝ)^k*((radialLinearLowLabels ε n k0).card:ℝ)^b/(d:ℝ)^n≤
        Real.exp (-((Real.log (d:ℝ)-(b:ℝ)*radialLinearEntropy d ε)/2)*n) := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hg : 0<(Real.log (d:ℝ)-(b:ℝ)*radialLinearEntropy d ε)/2 := by linarith
  filter_upwards [eventually_polynomial_le_exp C k hg] with n hp
  have hm := radialLinearLowLabels_card_le_entropy d n hd ε hε hεhalf k0 hcard
  have hpow : ((radialLinearLowLabels ε n k0).card:ℝ)^b≤
      Real.exp ((b:ℝ)*((n:ℝ)*radialLinearEntropy d ε)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) hm b
  have hD : (d:ℝ)^n=Real.exp ((n:ℝ)*Real.log (d:ℝ)) := by rw [Real.exp_nat_mul,Real.exp_log hd0]
  calc
    _ ≤ (Real.exp (((Real.log (d:ℝ)-(b:ℝ)*radialLinearEntropy d ε)/2)*n)*
        Real.exp ((b:ℝ)*((n:ℝ)*radialLinearEntropy d ε)))/(d:ℝ)^n := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hp hpow (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
    _ = _ := by rw [hD,← Real.exp_add,← Real.exp_sub]; congr 1; ring

/-- One fixed epsilon gives polynomial-times-m-squared/D exponential decay for every fixed polynomial prefactor. -/
theorem exists_radialLinearLowLabels_exponential (d : ℕ) (hd : 2≤d) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    ∃ ε c : ℝ,0<ε ∧ ε<1/2 ∧ radialLinearEntropy d ε<Real.log (d:ℝ)/2 ∧ 0<c ∧
      ∀ C : ℝ,∀ k : ℕ,∀ᶠ n : ℕ in atTop,
      C*(n:ℝ)^k*((radialLinearLowLabels ε n k0).card:ℝ)^2/(d:ℝ)^n≤Real.exp (-c*n) := by
  obtain ⟨ε,hε,hhalf,hgap⟩ := exists_radialLinearEntropy_gap d hd
  refine ⟨ε,(Real.log (d:ℝ)-2*radialLinearEntropy d ε)/2,hε,hhalf,hgap,by linarith,?_⟩
  intro C k
  exact radialLinearLowLabels_polynomial_ratio d hd ε hε hhalf k0 hcard C k 2 (by norm_num; linarith)

end CertificationGaussian
