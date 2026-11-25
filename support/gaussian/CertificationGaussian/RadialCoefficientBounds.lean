import CertificationGaussian.RadialCoefficientMass
import CertificationGaussian.ReadoutRemainderAsymptotics

noncomputable section
open Filter
open scoped BigOperators Topology
namespace CertificationGaussian

/-- A fixed coefficient constant, independent of system size and physical support weight. -/
def radialCoefficientPolynomialConstant (d r : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (r+1),(d:ℝ)^j.val*|lam j.val|

theorem radialCoefficientPolynomialConstant_nonneg (d r : ℕ) (lam : ℕ → ℝ) :
    0≤radialCoefficientPolynomialConstant d r lam := by
  unfold radialCoefficientPolynomialConstant
  positivity

/-- A direct finite-size polynomial bound: actual weights w are at most the number n of physical sites. -/
theorem radialFirstCoefficient_bound_of_le (d n r w : ℕ) (hn : 1≤n) (hw : w≤n) (lam : ℕ → ℝ) :
    |radialFirstCoefficient d r lam w| ≤
      radialCoefficientPolynomialConstant d r lam*(n:ℝ)^r*((d+1:ℝ)⁻¹)^w := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hs : (∑ j : Fin (r+1),(d:ℝ)^j.val*|lam j.val| *(w.choose j.val:ℝ))≤
      radialCoefficientPolynomialConstant d r lam*(n:ℝ)^r := by
    unfold radialCoefficientPolynomialConstant
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      (w.choose j.val:ℝ) ≤ (w:ℝ)^j.val := by exact_mod_cast Nat.choose_le_pow w j.val
      _ ≤ (n:ℝ)^j.val := pow_le_pow_left₀ (Nat.cast_nonneg w) (by exact_mod_cast hw) _
      _ ≤ (n:ℝ)^r := pow_le_pow_right₀ hn' (by omega)
  calc
    _ ≤ ((d+1:ℝ)⁻¹)^w * ∑ j : Fin (r+1),(d:ℝ)^j.val*|lam j.val| *(w.choose j.val:ℝ) :=
      radialFirstCoefficient_abs_le d r lam w
    _ ≤ ((d+1:ℝ)⁻¹)^w*(radialCoefficientPolynomialConstant d r lam*(n:ℝ)^r) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- The original integer cutoff used in the high/low Weyl decomposition. -/
def radialWeightCutoff (d r n : ℕ) : ℕ :=
  Nat.ceil (((2*r+24:ℕ):ℝ)*Real.log (n:ℝ)/Real.log (d+1:ℝ))

/-- The exact ceiling gives the intended inverse power, with no hidden asymptotic premise. -/
theorem radialWeightCutoff_geometric (d r n : ℕ) (hd : 1≤d) (hn : 1≤n) :
    ((d+1:ℝ)⁻¹)^(radialWeightCutoff d r n)≤((n:ℝ)^(2*r+24))⁻¹ := by
  have hq : (1:ℝ)<d+1 := by exact_mod_cast (show 1<d+1 by omega)
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlq : 0<Real.log (d+1:ℝ) := Real.log_pos hq
  have hc : (((2*r+24:ℕ):ℝ)*Real.log (n:ℝ)/Real.log (d+1:ℝ))≤
      (radialWeightCutoff d r n:ℝ) := Nat.le_ceil _
  have hl : (((2*r+24:ℕ):ℝ)*Real.log (n:ℝ))≤
      (radialWeightCutoff d r n:ℝ)*Real.log (d+1:ℝ) := (div_le_iff₀ hlq).mp hc
  have hp : (n:ℝ)^(2*r+24)≤(d+1:ℝ)^(radialWeightCutoff d r n) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simpa only [Real.log_pow] using hl
  rw [inv_pow]
  simpa only [one_div] using one_div_le_one_div_of_le
    (show (0:ℝ)<(n:ℝ)^(2*r+24) by positivity) hp

/-- Uniform high-weight bound for every physical support above the original cutoff. -/
theorem radialFirstCoefficient_high_bound (d n r w : ℕ) (hd : 1≤d) (hn : 1≤n)
    (hw : w≤n) (hL : radialWeightCutoff d r n<w) (lam : ℕ → ℝ) :
    |radialFirstCoefficient d r lam w| ≤
      radialCoefficientPolynomialConstant d r lam*((n:ℝ)^(r+24))⁻¹ := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (show 0<n by omega)
  have hq1 : (d+1:ℝ)⁻¹≤1 := by
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le
      (show (0:ℝ)<1 by norm_num) (show (1:ℝ)≤d+1 by nlinarith [Nat.cast_nonneg (α:=ℝ) d])
  have hq := (pow_le_pow_of_le_one (show (0:ℝ)≤(d+1:ℝ)⁻¹ by positivity) hq1 hL.le).trans
    (radialWeightCutoff_geometric d r n hd hn)
  calc
    _ ≤ radialCoefficientPolynomialConstant d r lam*(n:ℝ)^r*((d+1:ℝ)⁻¹)^w :=
      radialFirstCoefficient_bound_of_le d n r w hn hw lam
    _ ≤ radialCoefficientPolynomialConstant d r lam*(n:ℝ)^r*((n:ℝ)^(2*r+24))⁻¹ :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg (radialCoefficientPolynomialConstant_nonneg d r lam) (by positivity))
    _ = _ := by
      have he : 2*r+24=r+(r+24) := by omega
      rw [he,pow_add]
      field_simp

/-- The original second sequence is nonnegative for arbitrary signed lambda. -/
theorem radialSecondCoefficient_nonneg (d r w : ℕ) (lam : ℕ → ℝ) :
    0≤radialSecondCoefficient d r lam w := by
  unfold radialSecondCoefficient radialFirstCoefficient
  positivity

/-- The companion high-weight estimate retains the factor two and the squared original coefficients. -/
theorem radialSecondCoefficient_high_bound (d n r w : ℕ) (hd : 1≤d) (hn : 1≤n)
    (hw : w≤n) (hL : radialWeightCutoff d r n<w) (lam : ℕ → ℝ) :
    |radialSecondCoefficient d r lam w| ≤
      2*radialCoefficientPolynomialConstant d r (fun j => (lam j)^2)*((n:ℝ)^(r+24))⁻¹ := by
  have h := radialFirstCoefficient_high_bound d n r w hd hn hw hL (fun j => (lam j)^2)
  simpa only [radialSecondCoefficient,abs_mul,abs_of_nonneg (show (0:ℝ)≤2 by norm_num),mul_assoc] using
    mul_le_mul_of_nonneg_left h (show (0:ℝ)≤2 by norm_num)

/-- Every fixed first radial sequence has a finite uniform absolute bound over all natural weights. -/
theorem radialFirstCoefficient_bounded (d r : ℕ) (hd : 1≤d) (lam : ℕ → ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ w : ℕ,|radialFirstCoefficient d r lam w|≤C := by
  let B := radialCoefficientPolynomialConstant d r lam
  let κ : ℝ := (d+1:ℝ)⁻¹
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hq : (1:ℝ)<d+1 := by exact_mod_cast (show 1<d+1 by omega)
  have hκ1 : κ<1 := by
    dsimp [κ]
    simpa only [one_div,inv_one] using one_div_lt_one_div_of_lt (show (0:ℝ)<1 by norm_num) hq
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (eventually_polynomial_geometric_shift B r 0 hκ hκ1)
  let T := max N 1
  let C : ℝ := 1+∑ w∈Finset.range T,|radialFirstCoefficient d r lam w|
  have hsum : 0≤∑ w∈Finset.range T,|radialFirstCoefficient d r lam w| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro w
  by_cases hw : w<T
  · have hle := Finset.single_le_sum (fun v (_ : v∈Finset.range T) => abs_nonneg (radialFirstCoefficient d r lam v))
      (Finset.mem_range.mpr hw)
    dsimp [C]
    linarith
  · have hwN : N≤w := le_trans (le_max_left N 1) (Nat.le_of_not_gt hw)
    have hw1 : 1≤w := le_trans (le_max_right N 1) (Nat.le_of_not_gt hw)
    have hbound := radialFirstCoefficient_bound_of_le d w r w hw1 le_rfl lam
    have hgeom := hN w hwN
    simp only [Nat.sub_zero] at hgeom
    have he : Real.exp ((Real.log κ/2)*(w:ℝ))≤1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.log_neg hκ hκ1]) (Nat.cast_nonneg w)
    have hh : |radialFirstCoefficient d r lam w|≤1 := hbound.trans (hgeom.trans he)
    dsimp [C]
    linarith

/-- The original second sequence is uniformly bounded for fixed d,r,lambda as well. -/
theorem radialSecondCoefficient_bounded (d r : ℕ) (hd : 1≤d) (lam : ℕ → ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ w : ℕ,|radialSecondCoefficient d r lam w|≤C := by
  obtain ⟨C,hC,h⟩ := radialFirstCoefficient_bounded d r hd (fun j => (lam j)^2)
  refine ⟨2*C,by positivity,?_⟩
  intro w
  simpa only [radialSecondCoefficient,abs_mul,abs_of_nonneg (show (0:ℝ)≤2 by norm_num)] using
    mul_le_mul_of_nonneg_left (h w) (show (0:ℝ)≤2 by norm_num)

end CertificationGaussian
