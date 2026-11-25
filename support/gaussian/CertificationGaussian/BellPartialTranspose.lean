import CertificationGaussian.UnitaryBellFlattenings
import CertificationGaussian.PositiveTensorTrace

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual rank-one Bell projector already used inside weightedBellMatrix. -/
def unitaryBellProjector (U : Matrix I I ℂ) : Matrix (I × I) (I × I) ℂ :=
  Matrix.vecMulVec (fun p => unitaryBellVector U p) (fun p => star (unitaryBellVector U p))

/-- The unnormalized partial-transpose matrix, with precisely the existing first-factor convention. -/
def bellPartialTransposeUnitary (U : Matrix I I ℂ) : Matrix (I × I) (I × I) ℂ :=
  fun p q => U p.2 q.1*star (U q.2 p.1)

omit [DecidableEq I] in
/-- Partial transposition of a normalized Bell projector is exactly dimension^(-1) times the actual matrix above. -/
theorem unitaryBellProjector_partialTranspose (U : Matrix I I ℂ) :
    partialTransposeFirst (unitaryBellProjector U)=
      (Fintype.card I:ℂ)⁻¹ • bellPartialTransposeUnitary U := by
  have hs : (Real.sqrt (Fintype.card I:ℝ):ℂ)^2=(Fintype.card I:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I))
  ext ⟨i,r⟩ ⟨j,s⟩
  simp only [partialTransposeFirst,unitaryBellProjector,Matrix.vecMulVec_apply,
    unitaryBellVector,star_div₀,Complex.star_def,Complex.conj_ofReal,
    Matrix.smul_apply,smul_eq_mul,bellPartialTransposeUnitary]
  rw [div_mul_div_comm,← pow_two,hs]
  ring

omit [Fintype I] [DecidableEq I] in
/-- The scaled partial transpose is genuinely self-adjoint, even before imposing unitarity on U. -/
theorem bellPartialTransposeUnitary_star (U : Matrix I I ℂ) :
    star (bellPartialTransposeUnitary U)=bellPartialTransposeUnitary U := by
  ext p q
  simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,bellPartialTransposeUnitary,
    star_mul,star_star]

/-- Unitarity of the original matrix makes the actual scaled partial transpose an involution. -/
theorem bellPartialTransposeUnitary_mul_self (U : Matrix I I ℂ) (hU : U∈unitary (Matrix I I ℂ)) :
    bellPartialTransposeUnitary U*bellPartialTransposeUnitary U=1 := by
  ext ⟨i,r⟩ ⟨j,s⟩
  have hrow : (∑ k,U r k*star (U s k))=(1:Matrix I I ℂ) r s := by
    have h := congrArg (fun M : Matrix I I ℂ => M r s) hU.2
    simpa only [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply] using h
  have hcol : (∑ k,star (U k i)*U k j)=(1:Matrix I I ℂ) i j := by
    have h := congrArg (fun M : Matrix I I ℂ => M i j) hU.1
    simpa only [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply] using h
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,bellPartialTransposeUnitary]
  calc
    _ = (∑ k,U r k*star (U s k))*(∑ b,star (U b i)*U b j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      rw [hrow,hcol]
      simp only [Matrix.one_apply,Prod.mk.injEq]
      by_cases hij : i=j <;> by_cases hrs : r=s <;> simp [hij,hrs]

/-- The exact scaled partial transpose belongs to the genuine matrix unitary group. -/
theorem bellPartialTransposeUnitary_mem (U : Matrix I I ℂ) (hU : U∈unitary (Matrix I I ℂ)) :
    bellPartialTransposeUnitary U∈unitary (Matrix (I × I) (I × I) ℂ) := by
  constructor <;> rw [bellPartialTransposeUnitary_star,bellPartialTransposeUnitary_mul_self U hU]

/-- The true Euclidean operator norm of one Bell partial transpose is exactly 1/D, including the empty-coordinate case. -/
theorem unitaryBellProjector_partialTranspose_norm (U : Matrix I I ℂ)
    (hU : U∈unitary (Matrix I I ℂ)) :
    ‖Matrix.toEuclideanCLM (n:=I × I) (𝕜:=ℂ) (partialTransposeFirst (unitaryBellProjector U))‖=
      (Fintype.card I:ℝ)⁻¹ := by
  rw [Matrix.l2_opNorm_toEuclideanCLM,unitaryBellProjector_partialTranspose,norm_smul,
    norm_inv,Complex.norm_natCast]
  rcases isEmpty_or_nonempty I with h | h
  · let := h
    simp
  · let := h
    rw [CStarRing.norm_of_mem_unitary (bellPartialTransposeUnitary_mem U hU),mul_one]

omit [Fintype I] [DecidableEq I] in
theorem partialTransposeFirst_sum {K : Type*} [Fintype K]
    (A : K → Matrix (I × I) (I × I) ℂ) :
    partialTransposeFirst (∑ k,A k)=∑ k,partialTransposeFirst (A k) := by
  ext p q
  simp only [partialTransposeFirst,Matrix.sum_apply]

omit [Fintype I] [DecidableEq I] in
theorem partialTransposeFirst_smul (c : ℂ) (A : Matrix (I × I) (I × I) ℂ) :
    partialTransposeFirst (c • A)=c • partialTransposeFirst A := by
  ext p q
  rfl

omit [Fintype I] [DecidableEq I] in
theorem partialTransposeFirst_sub (A B : Matrix (I × I) (I × I) ℂ) :
    partialTransposeFirst (A-B)=partialTransposeFirst A-partialTransposeFirst B := by
  ext p q
  rfl

section Family
variable {K : Type*} [Fintype K]

/-- No Hilbert-Schmidt completeness or individual Hermiticity is needed for this true partial-transpose estimate. -/
theorem weightedBell_partialTranspose_norm_le (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w,W w∈unitary (Matrix I I ℂ)) :
    ‖Matrix.toEuclideanCLM (n:=I × I) (𝕜:=ℂ) (partialTransposeFirst (weightedBellMatrix W a))‖≤
      (∑ w,|a w|)/(Fintype.card I:ℝ) := by
  have hn (w : K) : ‖partialTransposeFirst (unitaryBellProjector (W w))‖=(Fintype.card I:ℝ)⁻¹ := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using unitaryBellProjector_partialTranspose_norm (W w) (hW w)
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  change ‖partialTransposeFirst (∑ w,(a w:ℂ) • unitaryBellProjector (W w))‖≤_
  rw [partialTransposeFirst_sum]
  simp only [partialTransposeFirst_smul]
  calc
    _ ≤ ∑ w,‖(a w:ℂ) • partialTransposeFirst (unitaryBellProjector (W w))‖ := norm_sum_le _ _
    _ = ∑ w,|a w| *(Fintype.card I:ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,hn]
    _ = _ := by rw [← Finset.sum_mul,div_eq_mul_inv]

omit [DecidableEq I] in
theorem weightedBellMatrix_sub (W : K → Matrix I I ℂ) (a b : K → ℝ) :
    weightedBellMatrix W (fun w => a w-b w)=weightedBellMatrix W a-weightedBellMatrix W b := by
  simp only [weightedBellMatrix,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

variable [DecidableEq K]

/-- Removing any actual finite set of Bell terms changes the true partially transposed Choi operator by at most its coefficient mass divided by D. -/
theorem weightedBell_partialTranspose_remove_bound (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w,W w∈unitary (Matrix I I ℂ)) (F : Finset K) :
    ‖Matrix.toEuclideanCLM (n:=I × I) (𝕜:=ℂ)
      (partialTransposeFirst (weightedBellMatrix W a)-
        partialTransposeFirst (weightedBellMatrix W (fun w => if w∈F then 0 else a w)))‖≤
      (∑ w∈F,|a w|)/(Fintype.card I:ℝ) := by
  have he : (fun w => a w-(if w∈F then 0 else a w))=(fun w => if w∈F then a w else 0) := by
    funext w
    by_cases h : w∈F <;> simp [h]
  rw [← partialTransposeFirst_sub,← weightedBellMatrix_sub,he]
  simpa [apply_ite abs] using weightedBell_partialTranspose_norm_le W (fun w => if w∈F then a w else 0) hW

/-- Removing a finite set F of Bell terms changes the partial transpose in operator norm by at most |F| ‖a‖∞ / D. -/
theorem weightedBell_partialTranspose_remove_card_bound (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w,W w∈unitary (Matrix I I ℂ)) (F : Finset K) :
    ‖Matrix.toEuclideanCLM (n:=I × I) (𝕜:=ℂ)
      (partialTransposeFirst (weightedBellMatrix W a)-
        partialTransposeFirst (weightedBellMatrix W (fun w => if w∈F then 0 else a w)))‖≤
      (F.card:ℝ)*‖a‖/(Fintype.card I:ℝ) := by
  refine (weightedBell_partialTranspose_remove_bound W a hW F).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ _w∈F,‖a‖ := Finset.sum_le_sum (fun w _ => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a w)
    _ = _ := by simp

end Family
end CertificationGaussian
