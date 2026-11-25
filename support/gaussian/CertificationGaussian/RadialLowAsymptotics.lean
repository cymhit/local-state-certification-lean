import CertificationGaussian.RadialLowCardinality

noncomputable section
open Filter
open scoped BigOperators Topology
namespace CertificationGaussian

/-- A fixed logarithmic-squared counting constant; no dependence on the system size. -/
def radialLowLogSquareConstant (d r k : ℕ) : ℝ :=
  ((((2*r+24:ℕ):ℝ)/Real.log (d+1:ℝ))+1)*(Real.log (((k-1:ℕ):ℝ)+1)+1)

theorem radialLowLogSquareConstant_pos (d r k : ℕ) (hd : 1≤d) :
    0<radialLowLogSquareConstant d r k := by
  have hq : 0<Real.log (d+1:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d+1 by omega))
  have hk : 0≤Real.log (((k-1:ℕ):ℝ)+1) := Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α:=ℝ) (k-1)])
  unfold radialLowLogSquareConstant
  positivity

/-- The actual low-label count is at most exp(C(1+log n)^2), with the original cutoff. -/
theorem radialLowLabels_card_le_exp_log_sq {K : Type*} [Fintype K] [DecidableEq K]
    (d r n : ℕ) (hd : 1≤d) (hn : 1≤n) (k0 : K) :
    ((radialLowLabels (S:=Fin n) d r k0).card:ℝ) ≤
      Real.exp (radialLowLogSquareConstant d r (Fintype.card K)*(1+Real.log (n:ℝ))^2) := by
  let L := radialWeightCutoff d r n
  let a : ℝ := ((Fintype.card K-1:ℕ):ℝ)
  let C : ℝ := ((2*r+24:ℕ):ℝ)/Real.log (d+1:ℝ)
  have ha : 0≤a := Nat.cast_nonneg _
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hl : 0≤Real.log (n:ℝ) := Real.log_nonneg hn1
  have hq : 0<Real.log (d+1:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d+1 by omega))
  have hC : 0≤C := by dsimp [C]; positivity
  have hla : 0≤Real.log (a+1) := Real.log_nonneg (by linarith)
  have hL : (L:ℝ)≤C*Real.log (n:ℝ)+1 := by
    have hx : 0≤(((2*r+24:ℕ):ℝ)*Real.log (n:ℝ)/Real.log (d+1:ℝ)) := by positivity
    have h := (Nat.ceil_lt_add_one hx).le
    dsimp [L,radialWeightCutoff,C]
    convert h using 1
    ring
  have hL' : (L:ℝ)≤(C+1)*(1+Real.log (n:ℝ)) := by nlinarith
  have hlogbase : Real.log ((n:ℝ)*a+1)≤Real.log (a+1)+Real.log (n:ℝ) := by
    calc
      _ ≤ Real.log ((a+1)*(n:ℝ)) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := Real.log_mul (by positivity) hn0.ne'
  have hp : ((n:ℝ)*a+1)^L≤Real.exp ((L:ℝ)*(Real.log (a+1)+Real.log (n:ℝ))) := by
    calc
      _ = Real.exp ((L:ℝ)*Real.log ((n:ℝ)*a+1)) := by rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlogbase (Nat.cast_nonneg L))
  have hf : (L:ℝ)+1≤Real.exp (L:ℝ) := by simpa only [add_comm] using Real.add_one_le_exp (L:ℝ)
  have hcount : ((radialLowLabels (S:=Fin n) d r k0).card:ℝ)≤((L:ℝ)+1)*((n:ℝ)*a+1)^L := by
    dsimp [L,a]
    exact_mod_cast radialLowLabels_card_le_power d r n k0
  calc
    _ ≤ ((L:ℝ)+1)*((n:ℝ)*a+1)^L := hcount
    _ ≤ Real.exp (L:ℝ)*Real.exp ((L:ℝ)*(Real.log (a+1)+Real.log (n:ℝ))) :=
      mul_le_mul hf hp (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((L:ℝ)*(1+Real.log (a+1)+Real.log (n:ℝ))) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ht : 1+Real.log (a+1)+Real.log (n:ℝ)≤(Real.log (a+1)+1)*(1+Real.log (n:ℝ)) := by
        nlinarith [mul_nonneg hla hl]
      have hmul := mul_le_mul hL' ht (by positivity : 0≤1+Real.log (a+1)+Real.log (n:ℝ))
        (by positivity : 0≤(C+1)*(1+Real.log (n:ℝ)))
      refine hmul.trans_eq ?_
      change ((C+1)*(1+Real.log (n:ℝ)))*((Real.log (a+1)+1)*(1+Real.log (n:ℝ)))=
        ((C+1)*(Real.log (a+1)+1))*(1+Real.log (n:ℝ))^2
      ring

/-- The logarithmic-squared factor is genuinely sublinear on the natural system-size sequence. -/
theorem eventually_one_add_log_sq_le {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,(1+Real.log (n:ℝ))^2≤ε*(n:ℝ) := by
  have h : (fun x : ℝ => (Real.log x)^2) =o[atTop] (fun x => x) := by
    simpa only [Real.rpow_two,Real.rpow_one] using
      isLittleO_log_rpow_rpow_atTop (s:=1) 2 (show (0:ℝ)<1 by norm_num)
  have hnat := h.comp_tendsto (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hnat.bound (show 0<ε/4 by positivity),hlog] with n hb hl
  simp only [Function.comp_def] at hl
  simp only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log (n:ℝ))),
    abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n)] at hb
  have hln : 0≤Real.log (n:ℝ) := by linarith
  nlinarith [mul_nonneg (show 0≤Real.log (n:ℝ)-1 by linarith) hln]

/-- Every positive linear exponential eventually dominates the actual low-label count. -/
theorem radialLowLabels_eventually_subexponential {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 1≤d) (k0 : K) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,((radialLowLabels (S:=Fin n) d r k0).card:ℝ)≤Real.exp (ε*n) := by
  let C := radialLowLogSquareConstant d r (Fintype.card K)
  have hC : 0<C := radialLowLogSquareConstant_pos d r _ hd
  filter_upwards [eventually_one_add_log_sq_le (show 0<ε/C by positivity),eventually_ge_atTop 1] with n hn hn1
  refine (radialLowLabels_card_le_exp_log_sq d r n hd hn1 k0).trans (Real.exp_le_exp.mpr ?_)
  calc
    C*(1+Real.log (n:ℝ))^2 ≤ C*((ε/C)*(n:ℝ)) := mul_le_mul_of_nonneg_left hn hC.le
    _ = ε*n := by field_simp

/-- Any fixed polynomial times any fixed power of the actual low-label count is exponentially small relative to d^n. -/
theorem radialLowLabels_polynomial_ratio_eventually {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (k0 : K) (C : ℝ) (k b : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*((radialLowLabels (S:=Fin n) d r k0).card:ℝ)^b/(d:ℝ)^n ≤
      Real.exp (-(Real.log (d:ℝ)/2)*n) := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hl : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  let ε : ℝ := Real.log (d:ℝ)/(4*((b:ℝ)+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hb : (b:ℝ)*ε≤Real.log (d:ℝ)/4 := by
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show (0:ℝ)<4*((b:ℝ)+1) by positivity)).mpr
    nlinarith
  filter_upwards [radialLowLabels_eventually_subexponential d r (by omega) k0 hε,
    eventually_polynomial_le_exp C k (show 0<Real.log (d:ℝ)/4 by positivity)] with n hm hp
  have hpow : ((radialLowLabels (S:=Fin n) d r k0).card:ℝ)^b≤Real.exp ((Real.log (d:ℝ)/4)*n) := by
    calc
      _ ≤ (Real.exp (ε*n))^b := pow_le_pow_left₀ (Nat.cast_nonneg _) hm b
      _ = Real.exp ((b:ℝ)*(ε*n)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) n])
  have hD : (d:ℝ)^n=Real.exp ((n:ℝ)*Real.log (d:ℝ)) := by rw [Real.exp_nat_mul,Real.exp_log hd0]
  calc
    _ ≤ (Real.exp ((Real.log (d:ℝ)/4)*n)*Real.exp ((Real.log (d:ℝ)/4)*n))/(d:ℝ)^n := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hp hpow (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
    _ = _ := by rw [hD,← Real.exp_add,← Real.exp_sub]; congr 1; ring

/-- A fixed negative exponential beats every inverse natural power. -/
theorem eventually_exp_neg_le_inverse_pow {a : ℝ} (ha : 0<a) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,Real.exp (-a*n)≤((n:ℝ)^k)⁻¹ := by
  filter_upwards [eventually_polynomial_le_exp 1 k ha,eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hpow : (n:ℝ)^k≤Real.exp (a*n) := by simpa only [one_mul] using hn
  have h := one_div_le_one_div_of_le (show (0:ℝ)<(n:ℝ)^k by positivity) hpow
  simpa only [one_div,← Real.exp_neg,neg_mul] using h

/-- The genuine low-label counting corrections vanish faster than every inverse polynomial. -/
theorem radialLowLabels_polynomial_ratio_inverse {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (k0 : K) (C : ℝ) (k b s : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*((radialLowLabels (S:=Fin n) d r k0).card:ℝ)^b/(d:ℝ)^n ≤
      ((n:ℝ)^s)⁻¹ := by
  have hl : 0<Real.log (d:ℝ)/2 := by
    have h := Real.log_pos (show (1:ℝ)<d by exact_mod_cast (show 1<d by omega))
    positivity
  filter_upwards [radialLowLabels_polynomial_ratio_eventually d r hd k0 C k b,
    eventually_exp_neg_le_inverse_pow hl s] with n hn he
  exact hn.trans he

end CertificationGaussian
