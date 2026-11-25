import CertificationGaussian.RadialBellWeights
import CertificationGaussian.ReadoutKernelAlgebra

noncomputable section
open scoped BigOperators
namespace CertificationGaussian
variable {K S : Type*} [Fintype K] [Fintype S] [DecidableEq K] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
/-- Exact sum of the local A0 weights for a full d^2-label family. -/
theorem radialBellAWeight_sum (d : ℕ) (k0 : K) (hcard : Fintype.card K=d^2) :
    (∑ k,radialBellAWeight d k0 k)=(d:ℝ) := by
  have he (k : K) : radialBellAWeight d k0 k=(d+1:ℝ)⁻¹+
      (if k=k0 then 1-(d+1:ℝ)⁻¹ else 0) := by
    by_cases h : k=k0 <;> simp [radialBellAWeight,h]
  simp only [he,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,hcard,Nat.cast_pow]
  have hq : (d+1:ℝ)≠0 := by positivity
  field_simp
  ring

omit [Fintype S] [DecidableEq S] in
/-- Exact sum of the local complementary weights. -/
theorem radialBellRWeight_sum (d : ℕ) (k0 : K) (hcard : Fintype.card K=d^2) :
    (∑ k,radialBellRWeight d k0 k)=(d:ℝ)-1 := by
  have he (k : K) : radialBellRWeight d k0 k=(d+1:ℝ)⁻¹-
      (if k=k0 then (d+1:ℝ)⁻¹ else 0) := by
    by_cases h : k=k0 <;> simp [radialBellRWeight,h]
  simp only [he,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,hcard,Nat.cast_pow]
  have hq : (d+1:ℝ)≠0 := by positivity
  field_simp
  ring

/-- Summing actual product labels factors by sites, with d-1 on each selected complement. -/
theorem radialBell_product_weight_sum (d : ℕ) (k0 : K) (hcard : Fintype.card K=d^2)
    (J : Finset S) :
    (∑ w : S → K,∏ s,if s∈J then radialBellRWeight d k0 (w s) else radialBellAWeight d k0 (w s))=
      ((d:ℝ)-1)^J.card*(d:ℝ)^(Fintype.card S-J.card) := by
  rw [← Fintype.prod_sum (fun s k => if s∈J then radialBellRWeight d k0 k else radialBellAWeight d k0 k)]
  have he : (∏ s : S,∑ k : K,if s∈J then radialBellRWeight d k0 k else radialBellAWeight d k0 k)=
      ∏ s : S,if s∈J then (d:ℝ)-1 else d := by
    apply Finset.prod_congr rfl
    intro s _
    by_cases hs : s∈J
    · simpa only [hs,ite_true] using radialBellRWeight_sum d k0 hcard
    · simpa only [hs,ite_false] using radialBellAWeight_sum d k0 hcard
  rw [he,Finset.prod_ite]
  simp [Finset.filter_not,Finset.card_sdiff]

/-- The exact original first weight sum is D times the existing trace scale h_n. -/
theorem radialFirstCoefficient_sum (d r : ℕ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    (∑ w : S → K,radialFirstCoefficient d r lam (radialBellSupport k0 w).card)=
      (d:ℝ)^(Fintype.card S)*cardinalityReadoutTraceScale d (Fintype.card S) r lam := by
  simp_rw [← radialBell_weight_formula d r lam k0]
  rw [Finset.sum_comm]
  unfold cardinalityReadoutTraceScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ J : {A : Finset S // A.card=j.val},
        (d:ℝ)^j.val*lam j.val*
          ∑ w : S → K,∏ s,if s∈J.val then radialBellRWeight d k0 (w s) else radialBellAWeight d k0 (w s) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ _J : {A : Finset S // A.card=j.val},
        (d:ℝ)^(Fintype.card S)*lam j.val*((d:ℝ)-1)^j.val := by
      apply Finset.sum_congr rfl
      intro J _
      rw [radialBell_product_weight_sum d k0 hcard J.val,J.property]
      have hj : j.val≤Fintype.card S := by rw [← J.property]; exact Finset.card_le_univ _
      have hp : (d:ℝ)^j.val*(d:ℝ)^(Fintype.card S-j.val)=(d:ℝ)^(Fintype.card S) := by
        rw [← pow_add,Nat.add_sub_of_le hj]
      calc
        _ = ((d:ℝ)^j.val*(d:ℝ)^(Fintype.card S-j.val))*lam j.val*((d:ℝ)-1)^j.val := by ring
        _ = _ := by rw [hp]
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_finset_len]
      ring

omit [Fintype K] [Fintype S] [DecidableEq K] [DecidableEq S] in
/-- Absolute values of signed radial coefficients are controlled by the same sequence with absolute coefficients. -/
theorem radialFirstCoefficient_abs_le (d r : ℕ) (lam : ℕ → ℝ) (w : ℕ) :
    |radialFirstCoefficient d r lam w|≤radialFirstCoefficient d r (fun j => |lam j|) w := by
  unfold radialFirstCoefficient
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤((d+1:ℝ)⁻¹)^w)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_mul,abs_mul,abs_pow,abs_of_nonneg (show (0:ℝ)≤d from Nat.cast_nonneg d),
    abs_of_nonneg (show (0:ℝ)≤(w.choose j.val:ℝ) from Nat.cast_nonneg _)]

/-- The original dimension-normalized absolute mass is bounded by the existing Lambda_n. -/
theorem radialFirstCoefficient_abs_mass (d r : ℕ) (hd : 0<d) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    ((d:ℝ)^(Fintype.card S))⁻¹ *
      ∑ w : S → K,|radialFirstCoefficient d r lam (radialBellSupport k0 w).card| ≤
        complementLambda d (Fintype.card S) r lam := by
  have hD : (0:ℝ)<(d:ℝ)^(Fintype.card S) := by positivity
  have hsum := Finset.sum_le_sum (fun w (_ : w∈(Finset.univ : Finset (S → K))) =>
    radialFirstCoefficient_abs_le d r lam (radialBellSupport k0 w).card)
  rw [radialFirstCoefficient_sum d r (fun j => |lam j|) k0 hcard] at hsum
  have ht : cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => |lam j|)=
      complementLambda d (Fintype.card S) r lam := rfl
  rw [ht] at hsum
  calc
    _ ≤ ((d:ℝ)^(Fintype.card S))⁻¹ *
        ((d:ℝ)^(Fintype.card S)*complementLambda d (Fintype.card S) r lam) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hD.ne',one_mul]

/-- The exact original second weight sum is 2D times the existing variance scale nu_n. -/
theorem radialSecondCoefficient_sum (d r : ℕ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    (∑ w : S → K,radialSecondCoefficient d r lam (radialBellSupport k0 w).card)=
      2*(d:ℝ)^(Fintype.card S)*cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => (lam j)^2) := by
  simp only [radialSecondCoefficient,← Finset.mul_sum,radialFirstCoefficient_sum d r _ k0 hcard]
  ring

end CertificationGaussian
