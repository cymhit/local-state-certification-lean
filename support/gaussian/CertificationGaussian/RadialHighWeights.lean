import CertificationGaussian.RadialCoefficientBounds

noncomputable section
open scoped BigOperators
namespace CertificationGaussian
variable {K S : Type*} [Fintype K] [Fintype S] [DecidableEq K] [DecidableEq S]

/-- The actual first radial weights after deleting all labels at or below the original cutoff. -/
def radialFirstHighWeights (d r : ℕ) (lam : ℕ → ℝ) (k0 : K) (w : S → K) : ℝ :=
  if radialWeightCutoff d r (Fintype.card S)<(radialBellSupport k0 w).card
    then radialFirstCoefficient d r lam (radialBellSupport k0 w).card else 0

/-- The actual second radial weights with exactly the same physical cutoff. -/
def radialSecondHighWeights (d r : ℕ) (lam : ℕ → ℝ) (k0 : K) (w : S → K) : ℝ :=
  if radialWeightCutoff d r (Fintype.card S)<(radialBellSupport k0 w).card
    then radialSecondCoefficient d r lam (radialBellSupport k0 w).card else 0

/-- The actual low-weight label set; no independent cardinality or cutoff hypothesis is inserted. -/
def radialLowLabels (d r : ℕ) (k0 : K) : Finset (S → K) :=
  Finset.univ.filter (fun w => (radialBellSupport k0 w).card≤radialWeightCutoff d r (Fintype.card S))

theorem radialFirstHighWeights_remove (d r : ℕ) (lam : ℕ → ℝ) (k0 : K) :
    radialFirstHighWeights (S:=S) d r lam k0=
      (fun w => if w∈radialLowLabels d r k0 then 0 else radialFirstCoefficient d r lam (radialBellSupport k0 w).card) := by
  funext w
  simp only [radialFirstHighWeights,radialLowLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> first | rfl | omega

omit [Fintype K] [DecidableEq S] in
/-- All actual high weights satisfy the original n^(-r-24) estimate. -/
theorem radialFirstHighWeights_abs_le (d r : ℕ) (hd : 1≤d) (hn : 1≤Fintype.card S)
    (lam : ℕ → ℝ) (k0 : K) (w : S → K) :
    |radialFirstHighWeights d r lam k0 w| ≤
      radialCoefficientPolynomialConstant d r lam*((Fintype.card S:ℝ)^(r+24))⁻¹ := by
  unfold radialFirstHighWeights
  split_ifs with h
  · exact radialFirstCoefficient_high_bound d (Fintype.card S) r _ hd hn
      (Finset.card_le_univ _) h lam
  · simpa only [abs_zero] using mul_nonneg (radialCoefficientPolynomialConstant_nonneg d r lam)
      (by positivity : (0:ℝ)≤((Fintype.card S:ℝ)^(r+24))⁻¹)

/-- The actual supremum coefficient norm entering Gaussian chaos is controlled. -/
theorem radialFirstHighWeights_norm_le (d r : ℕ) (hd : 1≤d) (hn : 1≤Fintype.card S)
    (lam : ℕ → ℝ) (k0 : K) :
    ‖radialFirstHighWeights (S:=S) d r lam k0‖ ≤
      radialCoefficientPolynomialConstant d r lam*((Fintype.card S:ℝ)^(r+24))⁻¹ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (radialCoefficientPolynomialConstant_nonneg d r lam) (by positivity))).mpr
  intro w
  simpa only [Real.norm_eq_abs] using radialFirstHighWeights_abs_le d r hd hn lam k0 w

/-- Truncation cannot increase the original dimension-normalized absolute mass. -/
theorem radialFirstHighWeights_abs_mass (d r : ℕ) (hd : 0<d) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    ((d:ℝ)^(Fintype.card S))⁻¹ * ∑ w : S → K,|radialFirstHighWeights d r lam k0 w| ≤
      complementLambda d (Fintype.card S) r lam := by
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) (by positivity))
    (radialFirstCoefficient_abs_mass d r hd lam k0 hcard)
  unfold radialFirstHighWeights
  split_ifs <;> simp [abs_nonneg]

/-- A finite scalar inequality applied below to the actual high weights, not assumed as a matrix bound. -/
theorem finite_square_mass_le {T : Type*} [Fintype T] (a : T → ℝ) {D C M : ℝ}
    (hD : 0<D) (hC : 0≤C) (hmax : ∀ t,|a t|≤C) (hmass : D⁻¹*∑ t,|a t|≤M) :
    (∑ t,(a t)^2)/D≤C*M := by
  have hs : (∑ t,(a t)^2)≤C*∑ t,|a t| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    have ht := mul_le_mul_of_nonneg_right (hmax t) (abs_nonneg (a t))
    simpa only [← pow_two,sq_abs] using ht
  calc
    _ ≤ (C*∑ t,|a t|)/D := div_le_div_of_nonneg_right hs hD.le
    _ = C*(D⁻¹*∑ t,|a t|) := by ring
    _ ≤ C*M := mul_le_mul_of_nonneg_left hmass hC

/-- Exact dimension-normalized high-weight square mass, with no factor growing exponentially in n. -/
theorem radialFirstHighWeights_square_mass (d r : ℕ) (hd : 1≤d) (hn : 1≤Fintype.card S)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    (∑ w : S → K,(radialFirstHighWeights d r lam k0 w)^2)/(d:ℝ)^(Fintype.card S) ≤
      radialCoefficientPolynomialConstant d r lam*complementLambdaCoefficient d r lam*
        ((Fintype.card S:ℝ)^24)⁻¹ := by
  have hB := radialCoefficientPolynomialConstant_nonneg d r lam
  have hA := complementLambdaCoefficient_nonneg d r hd lam
  have hn0 : (Fintype.card S:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (show 0<Fintype.card S by omega)
  have hm := (radialFirstHighWeights_abs_mass d r (by omega) lam k0 hcard).trans
    (complementLambda_le_polynomial d (Fintype.card S) r hd hn lam)
  have h := finite_square_mass_le (radialFirstHighWeights (S:=S) d r lam k0)
    (by positivity : (0:ℝ)<(d:ℝ)^(Fintype.card S))
    (mul_nonneg hB (by positivity)) (radialFirstHighWeights_abs_le d r hd hn lam k0) hm
  refine h.trans_eq ?_
  rw [pow_add]
  field_simp

/-- The variance scale in the Gaussian chaos theorem is O(n^-12), with an explicit fixed constant. -/
theorem radialFirstHighWeights_sqrt_square_mass (d r : ℕ) (hd : 1≤d) (hn : 1≤Fintype.card S)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    Real.sqrt ((∑ w : S → K,(radialFirstHighWeights d r lam k0 w)^2)/(d:ℝ)^(Fintype.card S)) ≤
      Real.sqrt (radialCoefficientPolynomialConstant d r lam*complementLambdaCoefficient d r lam)*
        ((Fintype.card S:ℝ)^12)⁻¹ := by
  refine (Real.sqrt_le_sqrt (radialFirstHighWeights_square_mass d r hd hn lam k0 hcard)).trans_eq ?_
  rw [Real.sqrt_mul (mul_nonneg (radialCoefficientPolynomialConstant_nonneg d r lam)
    (complementLambdaCoefficient_nonneg d r hd lam)),Real.sqrt_inv]
  have hp : (Fintype.card S:ℝ)^24=((Fintype.card S:ℝ)^12)^2 := by ring
  rw [hp,Real.sqrt_sq (by positivity)]

omit [Fintype K] [DecidableEq S] in
/-- The second truncation is exactly twice the first truncation with the squared coefficients. -/
theorem radialSecondHighWeights_eq (d r : ℕ) (lam : ℕ → ℝ) (k0 : K) (w : S → K) :
    radialSecondHighWeights d r lam k0 w=2*radialFirstHighWeights d r (fun j => (lam j)^2) k0 w := by
  simp only [radialSecondHighWeights,radialFirstHighWeights,radialSecondCoefficient]
  split_ifs <;> simp

/-- Supremum bound for the actual second high-weight coefficient function. -/
theorem radialSecondHighWeights_norm_le (d r : ℕ) (hd : 1≤d) (hn : 1≤Fintype.card S)
    (lam : ℕ → ℝ) (k0 : K) :
    ‖radialSecondHighWeights (S:=S) d r lam k0‖ ≤
      2*radialCoefficientPolynomialConstant d r (fun j => (lam j)^2)*((Fintype.card S:ℝ)^(r+24))⁻¹ := by
  have he : radialSecondHighWeights (S:=S) d r lam k0=
      (2:ℝ) • radialFirstHighWeights d r (fun j => (lam j)^2) k0 := by
    funext w
    exact radialSecondHighWeights_eq d r lam k0 w
  rw [he,norm_smul,Real.norm_of_nonneg (show (0:ℝ)≤2 by norm_num)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (radialFirstHighWeights_norm_le d r hd hn (fun j => (lam j)^2) k0) (show (0:ℝ)≤2 by norm_num)

/-- The actual second Gaussian variance scale is also O(n^-12), with all factors explicit. -/
theorem radialSecondHighWeights_sqrt_square_mass (d r : ℕ) (hd : 1≤d) (hn : 1≤Fintype.card S)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    Real.sqrt ((∑ w : S → K,(radialSecondHighWeights d r lam k0 w)^2)/(d:ℝ)^(Fintype.card S)) ≤
      2*Real.sqrt (radialCoefficientPolynomialConstant d r (fun j => (lam j)^2)*
        complementLambdaCoefficient d r (fun j => (lam j)^2))*((Fintype.card S:ℝ)^12)⁻¹ := by
  have he : (∑ w : S → K,(radialSecondHighWeights d r lam k0 w)^2)/(d:ℝ)^(Fintype.card S)=
      4*((∑ w : S → K,(radialFirstHighWeights d r (fun j => (lam j)^2) k0 w)^2)/(d:ℝ)^(Fintype.card S)) := by
    simp only [radialSecondHighWeights_eq,mul_pow,← Finset.mul_sum]
    ring
  rw [he,Real.sqrt_mul (show (0:ℝ)≤4 by norm_num)]
  rw [show Real.sqrt (4:ℝ)=2 by
    simpa only [show (2:ℝ)^2=4 by norm_num] using Real.sqrt_sq (show (0:ℝ)≤2 by norm_num)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (radialFirstHighWeights_sqrt_square_mass d r hd hn (fun j => (lam j)^2) k0 hcard)
    (show (0:ℝ)≤2 by norm_num)

/-- The actual scalar sigma in the centered Gaussian high operator has the original polynomial bound. -/
theorem radialFirstHighWeights_mean_abs_le (d r : ℕ) (hd : 1≤d) (hn : 1≤Fintype.card S)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    |(∑ w : S → K,radialFirstHighWeights d r lam k0 w)/(d:ℝ)^(Fintype.card S)| ≤
      complementLambdaCoefficient d r lam*(Fintype.card S:ℝ)^r := by
  rw [abs_div,abs_of_nonneg (show (0:ℝ)≤(d:ℝ)^(Fintype.card S) by positivity)]
  calc
    _ ≤ (∑ w : S → K,|radialFirstHighWeights d r lam k0 w|)/(d:ℝ)^(Fintype.card S) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ((d:ℝ)^(Fintype.card S))⁻¹ * ∑ w : S → K,|radialFirstHighWeights d r lam k0 w| := by ring
    _ ≤ complementLambda d (Fintype.card S) r lam := radialFirstHighWeights_abs_mass d r (by omega) lam k0 hcard
    _ ≤ _ := complementLambda_le_polynomial d (Fintype.card S) r hd hn lam

/-- The second high operator mean has the same fixed polynomial order. -/
theorem radialSecondHighWeights_mean_abs_le (d r : ℕ) (hd : 1≤d) (hn : 1≤Fintype.card S)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    |(∑ w : S → K,radialSecondHighWeights d r lam k0 w)/(d:ℝ)^(Fintype.card S)| ≤
      2*complementLambdaCoefficient d r (fun j => (lam j)^2)*(Fintype.card S:ℝ)^r := by
  simp only [radialSecondHighWeights_eq,← Finset.mul_sum,mul_div_assoc,abs_mul,
    abs_of_nonneg (show (0:ℝ)≤2 by norm_num)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (radialFirstHighWeights_mean_abs_le d r hd hn (fun j => (lam j)^2) k0 hcard)
    (show (0:ℝ)≤2 by norm_num)

end CertificationGaussian
