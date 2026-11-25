import CertificationGaussian.ReadoutRemainderTail
import CertificationGaussian.TailAsymptotics
import Mathlib.Data.Nat.Choose.Bounds

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

/-- A fixed coefficient constant for the original paper Lambda; independent of the system size. -/
def complementLambdaCoefficient (d r : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (r+1), |lam j| *((d:ℝ)-1)^(j:ℕ)

theorem complementLambdaCoefficient_nonneg (d r : ℕ) (hd : 1≤d) (lam : ℕ → ℝ) :
    0≤complementLambdaCoefficient d r lam := by
  have hd' : (0:ℝ)≤(d:ℝ)-1 := by
    have h : (1:ℝ)≤d := by exact_mod_cast hd
    linarith
  unfold complementLambdaCoefficient
  positivity

/-- The genuine binomial Lambda grows at most like n^r, including signed or zero coefficients. -/
theorem complementLambda_le_polynomial (d n r : ℕ) (hd : 1≤d) (hn : 1≤n) (lam : ℕ → ℝ) :
    complementLambda d n r lam ≤ complementLambdaCoefficient d r lam*(n:ℝ)^r := by
  have hd' : (0:ℝ)≤(d:ℝ)-1 := by
    have h : (1:ℝ)≤d := by exact_mod_cast hd
    linarith
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  unfold complementLambda complementLambdaCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hj : (n.choose (j:ℕ):ℝ)≤(n:ℝ)^r := by
    calc
      _ ≤ (n:ℝ)^(j:ℕ) := by exact_mod_cast Nat.choose_le_pow n (j:ℕ)
      _ ≤ _ := pow_le_pow_right₀ hn' (by omega)
  calc
    _ ≤ |lam j| *(n:ℝ)^r*((d:ℝ)-1)^(j:ℕ) := by gcongr
    _ = _ := by ring

/-- Any fixed polynomial times a shifted strict geometric factor is eventually exponentially small. -/
theorem eventually_polynomial_geometric_shift (C : ℝ) (k q : ℕ)
    {κ : ℝ} (hκ : 0<κ) (hκ1 : κ<1) :
    ∀ᶠ n : ℕ in atTop, C*(n:ℝ)^k*κ^(n-q) ≤ Real.exp ((Real.log κ/2)*n) := by
  have hl : Real.log κ<0 := Real.log_neg hκ hκ1
  filter_upwards [eventually_polynomial_le_exp (C/κ^q) k (show 0< -(Real.log κ/2) by linarith),
    eventually_ge_atTop q] with n hn hnq
  calc
    _ = (C/κ^q)*(n:ℝ)^k*κ^n := by rw [pow_sub₀ κ hκ.ne' hnq]; ring
    _ ≤ Real.exp (-(Real.log κ/2)*n)*κ^n := mul_le_mul_of_nonneg_right hn (pow_nonneg hκ.le _)
    _ = Real.exp (-(Real.log κ/2)*n)*Real.exp ((n:ℝ)*Real.log κ) := by rw [Real.exp_nat_mul,Real.exp_log hκ]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The original Lambda prefactor, including n^12 and the 8r shift, is absorbed with a fixed exponential rate. -/
theorem eventually_remainder_prefactor (d r : ℕ) (hd : 1≤d) (lam : ℕ → ℝ)
    {C κ : ℝ} (hC : 0≤C) (hκ : 0<κ) (hκ1 : κ<1) :
    ∀ᶠ n : ℕ in atTop,
      (n:ℝ)^12*C*(complementLambda d n r lam)^8*κ^(n-8*r) ≤
        Real.exp ((Real.log κ/2)*n) := by
  let B := complementLambdaCoefficient d r lam
  have hB : 0≤B := complementLambdaCoefficient_nonneg d r hd lam
  have hd' : (0:ℝ)≤(d:ℝ)-1 := by
    have h : (1:ℝ)≤d := by exact_mod_cast hd
    linarith
  filter_upwards [eventually_polynomial_geometric_shift (C*B^8) (12+8*r) (8*r) hκ hκ1,
    eventually_ge_atTop 1] with n hn hn1
  have hΛ : 0≤complementLambda d n r lam := by unfold complementLambda; positivity
  have hbound := complementLambda_le_polynomial d n r hd hn1 lam
  calc
    _ ≤ (n:ℝ)^12*C*(B*(n:ℝ)^r)^8*κ^(n-8*r) := by gcongr
    _ = (C*B^8)*(n:ℝ)^(12+8*r)*κ^(n-8*r) := by rw [mul_pow,← pow_mul,pow_add]; congr 1; ring_nf
    _ ≤ _ := hn

/-- For fixed d,r and signed coefficients, the actual full-Haar remainder event has exponential probability decay. -/
theorem cardinalityHaar_remainder_eventually_exponential (d r : ℕ) [NeZero d]
    (hd : 3≤d) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
    pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal (Real.exp ((Real.log (haarLocalKappa d)/2)*n)) := by
  have hκ := haarLocalKappa_pos d (by omega)
  have hp := eventually_remainder_prefactor d r (by omega) lam
    (C:=(Nat.factorial 8:ℝ)*((d:ℝ)^4*((d:ℝ)-1)^8)^(8*r)) (by positivity)
    hκ (haarLocalKappa_lt_one d hd)
  filter_upwards [hp,eventually_ge_atTop 1] with n hn hn1
  exact (cardinalityHaar_remainder_tail_n_inv_three d n r hd (by omega) lam).trans
    (ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using hn))

/-- The same exponential conclusion holds for the actual finite three-Pauli-basis remainder. -/
theorem cardinalityPauli_remainder_eventually_exponential (r : ℕ) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
    pairedGaussian (QuditIndex 2 n) {x | ((n:ℝ)^3)⁻¹<‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
      (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖} ≤
      ENNReal.ofReal (Real.exp ((Real.log pauliLocalKappa/2)*n)) := by
  have hp := eventually_remainder_prefactor 2 r (by decide) lam
    (C:=(Nat.factorial 8:ℝ)*(16:ℝ)^(8*r)) (by positivity)
    pauliLocalKappa_pos pauliLocalKappa_lt_one
  filter_upwards [hp,eventually_ge_atTop 1] with n hn hn1
  exact (cardinalityPauli_remainder_tail_n_inv_three n r (by omega) lam).trans
    (ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using hn))

end CertificationGaussian
