import CertificationGaussian.RadialLinearCardinality
import CertificationGaussian.RadialHighWeights

noncomputable section
open Filter
open scoped BigOperators Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The original first radial weights above the fixed linear support cutoff. -/
def radialLinearFirstHighWeights (d n r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (k0 : K) (w : Fin n → K) : ℝ :=
  if radialLinearWeightCutoff ε n<(radialBellSupport k0 w).card
    then radialFirstCoefficient d r lam (radialBellSupport k0 w).card else 0

/-- The original second weights with exactly the same fixed linear cutoff. -/
def radialLinearSecondHighWeights (d n r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (k0 : K) (w : Fin n → K) : ℝ :=
  if radialLinearWeightCutoff ε n<(radialBellSupport k0 w).card
    then radialSecondCoefficient d r lam (radialBellSupport k0 w).card else 0

theorem radialLinearFirstHighWeights_remove (d n r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (k0 : K) :
    radialLinearFirstHighWeights d n r ε lam k0=
      (fun w => if w∈radialLinearLowLabels ε n k0 then 0 else
        radialFirstCoefficient d r lam (radialBellSupport k0 w).card) := by
  funext w
  simp only [radialLinearFirstHighWeights,radialLinearLowLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> first | rfl | omega

/-- A support strictly above floor(epsilon*n) is already above epsilon*n itself. -/
theorem radialLinearCutoff_geometric (d n w : ℕ) (hd : 1≤d) (ε : ℝ)
    (hw : radialLinearWeightCutoff ε n<w) :
    ((d+1:ℝ)⁻¹)^w≤Real.exp (-(ε*Real.log (d+1:ℝ))*n) := by
  have hq : (1:ℝ)<d+1 := by exact_mod_cast (show 1<d+1 by omega)
  have hlt := Nat.lt_floor_add_one (ε*(n:ℝ))
  have hw' : ((Nat.floor (ε*(n:ℝ))+1:ℕ):ℝ)≤w := by
    exact_mod_cast (show Nat.floor (ε*(n:ℝ))+1≤w by unfold radialLinearWeightCutoff at hw; omega)
  have he : ((d+1:ℝ)⁻¹)^w=Real.exp (-((w:ℝ)*Real.log (d+1:ℝ))) := by
    rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by positivity),inv_pow]
  rw [he]
  apply Real.exp_le_exp.mpr
  have hl : 0<Real.log (d+1:ℝ) := Real.log_pos hq
  norm_num only [Nat.cast_add,Nat.cast_one] at hw'
  nlinarith

omit [Fintype K] in
/-- Actual high coefficients have an exponentially decaying geometric factor, with the original polynomial coefficient. -/
theorem radialLinearFirstHighWeights_abs_le (d n r : ℕ) (hd : 1≤d) (hn : 1≤n)
    (ε : ℝ) (lam : ℕ → ℝ) (k0 : K) (w : Fin n → K) :
    |radialLinearFirstHighWeights d n r ε lam k0 w|≤
      radialCoefficientPolynomialConstant d r lam*(n:ℝ)^r*
        Real.exp (-(ε*Real.log (d+1:ℝ))*n) := by
  unfold radialLinearFirstHighWeights
  split_ifs with h
  · have hw : (radialBellSupport k0 w).card≤n := by simpa using Finset.card_le_univ (radialBellSupport k0 w)
    exact (radialFirstCoefficient_bound_of_le d n r _ hn hw lam).trans
      (mul_le_mul_of_nonneg_left (radialLinearCutoff_geometric d n _ hd ε h)
        (mul_nonneg (radialCoefficientPolynomialConstant_nonneg d r lam) (by positivity)))
  · simpa only [abs_zero] using mul_nonneg
      (mul_nonneg (radialCoefficientPolynomialConstant_nonneg d r lam) (by positivity)) (Real.exp_nonneg _)

/-- Actual normalized absolute mass cannot increase under this linear truncation. -/
theorem radialLinearFirstHighWeights_abs_mass (d n r : ℕ) (hd : 0<d) (ε : ℝ)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ((d:ℝ)^n)⁻¹*∑ w : Fin n → K,|radialLinearFirstHighWeights d n r ε lam k0 w|≤
      complementLambda d n r lam := by
  have hf : ((d:ℝ)^n)⁻¹*∑ w : Fin n → K,|radialFirstCoefficient d r lam (radialBellSupport k0 w).card|≤
      complementLambda d n r lam := by
    simpa only [Fintype.card_fin] using radialFirstCoefficient_abs_mass (S:=Fin n) d r hd lam k0 hcard
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) (by positivity)).trans hf
  unfold radialLinearFirstHighWeights
  split_ifs <;> simp [abs_nonneg]

/-- The actual supremum coefficient parameter is exponentially small at a fixed positive linear cutoff. -/
theorem radialLinearFirstHighWeights_norm_eventually (d r : ℕ) (hd : 1≤d)
    (ε : ℝ) (hε : 0<ε) (lam : ℕ → ℝ) (k0 : K) :
    ∀ᶠ n : ℕ in atTop,‖radialLinearFirstHighWeights d n r ε lam k0‖≤
      Real.exp (-((ε*Real.log (d+1:ℝ))/2)*n) := by
  have ha : 0<(ε*Real.log (d+1:ℝ))/2 := by
    apply div_pos (mul_pos hε (Real.log_pos ?_)) (by norm_num)
    exact_mod_cast (show 1<d+1 by omega)
  filter_upwards [eventually_polynomial_le_exp (radialCoefficientPolynomialConstant d r lam) r ha,
    eventually_ge_atTop 1] with n hp hn
  apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
  intro w
  calc
    ‖radialLinearFirstHighWeights d n r ε lam k0 w‖≤
        radialCoefficientPolynomialConstant d r lam*(n:ℝ)^r*Real.exp (-(ε*Real.log (d+1:ℝ))*n) :=
      radialLinearFirstHighWeights_abs_le d n r hd hn ε lam k0 w
    _ ≤ Real.exp (((ε*Real.log (d+1:ℝ))/2)*n)*Real.exp (-(ε*Real.log (d+1:ℝ))*n) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The dimension-normalized square mass has exponential decay, with no loss depending exponentially on dimension. -/
theorem radialLinearFirstHighWeights_square_eventually (d r : ℕ) (hd : 1≤d)
    (ε : ℝ) (hε : 0<ε) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,
      (∑ w : Fin n → K,(radialLinearFirstHighWeights d n r ε lam k0 w)^2)/(d:ℝ)^n≤
        Real.exp (-((ε*Real.log (d+1:ℝ))/2)*n) := by
  let B := radialCoefficientPolynomialConstant d r lam
  let A := complementLambdaCoefficient d r lam
  have ha : 0<(ε*Real.log (d+1:ℝ))/2 := by
    apply div_pos (mul_pos hε (Real.log_pos ?_)) (by norm_num)
    exact_mod_cast (show 1<d+1 by omega)
  filter_upwards [eventually_polynomial_le_exp (B*A) (2*r) ha,eventually_ge_atTop 1] with n hp hn
  have hm := (radialLinearFirstHighWeights_abs_mass d n r (by omega) ε lam k0 hcard).trans
    (complementLambda_le_polynomial d n r hd hn lam)
  have hs := finite_square_mass_le (radialLinearFirstHighWeights d n r ε lam k0)
    (by positivity : (0:ℝ)<(d:ℝ)^n)
    (mul_nonneg (mul_nonneg (radialCoefficientPolynomialConstant_nonneg d r lam) (by positivity))
      (Real.exp_nonneg _)) (radialLinearFirstHighWeights_abs_le d n r hd hn ε lam k0) hm
  calc
    _ ≤ (B*(n:ℝ)^r*Real.exp (-(ε*Real.log (d+1:ℝ))*n))*(A*(n:ℝ)^r) := hs
    _ = (B*A)*(n:ℝ)^(2*r)*Real.exp (-(ε*Real.log (d+1:ℝ))*n) := by ring
    _ ≤ Real.exp (((ε*Real.log (d+1:ℝ))/2)*n)*Real.exp (-(ε*Real.log (d+1:ℝ))*n) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The square-root parameter of the actual Gaussian chaos theorem is exponentially small as well. -/
theorem radialLinearFirstHighWeights_sqrt_eventually (d r : ℕ) (hd : 1≤d)
    (ε : ℝ) (hε : 0<ε) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((∑ w : Fin n → K,(radialLinearFirstHighWeights d n r ε lam k0 w)^2)/(d:ℝ)^n)≤
        Real.exp (-((ε*Real.log (d+1:ℝ))/4)*n) := by
  filter_upwards [radialLinearFirstHighWeights_square_eventually d r hd ε hε lam k0 hcard] with n hn
  refine (Real.sqrt_le_sqrt hn).trans_eq ?_
  have he : Real.exp (-((ε*Real.log (d+1:ℝ))/2)*n)=
      (Real.exp (-((ε*Real.log (d+1:ℝ))/4)*n))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he,Real.sqrt_sq (Real.exp_nonneg _)]

omit [Fintype K] in
/-- The companion remains exactly twice the same first truncation with squared original coefficients. -/
theorem radialLinearSecondHighWeights_eq (d n r : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (k0 : K) (w : Fin n → K) :
    radialLinearSecondHighWeights d n r ε lam k0 w=
      2*radialLinearFirstHighWeights d n r ε (fun j => (lam j)^2) k0 w := by
  simp only [radialLinearSecondHighWeights,radialLinearFirstHighWeights,radialSecondCoefficient]
  split_ifs <;> simp

end CertificationGaussian
