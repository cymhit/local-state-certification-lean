import CertificationGaussian.ReadoutRadialSpectrum
import CertificationGaussian.RadialLowOrbit

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- The diagonal sandwich of the genuine orbit columns is the actual weighted sum of conjugated rank-one projectors. -/
theorem unitaryOrbitMatrix_diagonal (W : K → Matrix I I ℂ) (a : K → ℝ)
    (ψ : EuclideanSpace ℂ I) :
    unitaryOrbitMatrix W ψ*Matrix.diagonal (fun w => (a w:ℂ))*(unitaryOrbitMatrix W ψ)ᴴ=
      ∑ w,(a w:ℂ) • (W w*Matrix.vecMulVec ψ.ofLp (fun i => star (ψ.ofLp i))*(W w)ᴴ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro w _
  have hr : W w*Matrix.vecMulVec ψ.ofLp (fun i => star (ψ.ofLp i))*(W w)ᴴ=
      Matrix.vecMulVec ((W w)*ᵥψ.ofLp) (star ((W w)*ᵥψ.ofLp)) := by
    rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.star_mulVec]
    rfl
  have hV (i : I) : unitaryOrbitMatrix W ψ i w=((W w)*ᵥψ.ofLp) i := rfl
  rw [hr]
  simp only [Matrix.vecMulVec_apply,Pi.star_apply,hV]
  ring

/-- Actual finite-subset orbit compression, with no dimension loss or independent coefficient surrogate. -/
theorem unitarySphereConjugation_finset [Nonempty I]
    (W : K → Matrix I I ℂ) (a : K → ℝ) (F : Finset K) (ψ : EuclideanSpace ℂ I) :
    unitarySphereConjugation W (fun w => if w∈F then a w else 0) ψ=
      rectangularEuclideanCLM
        (unitaryOrbitMatrix (fun w : F => W w.val) ψ*
          Matrix.diagonal (fun w : F => (a w.val:ℂ))*(unitaryOrbitMatrix (fun w : F => W w.val) ψ)ᴴ) := by
  rw [unitarySphereConjugation_eq_sum,unitaryOrbitMatrix_diagonal]
  congr 1
  simp only [apply_ite Complex.ofReal,Complex.ofReal_zero,ite_smul,zero_smul]
  rw [← Finset.sum_filter]
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using
    Finset.sum_subtype F (fun _ => Iff.rfl)
      (fun w => (a w:ℂ) • (W w*Matrix.vecMulVec ψ.ofLp (fun i => star (ψ.ofLp i))*(W w)ᴴ))

omit [DecidableEq K] in
/-- Exact additivity of the same centered sphere operator in its real weights. -/
theorem unitarySphereCentered_add (W : K → Matrix I I ℂ) (a b : K → ℝ)
    (ψ : EuclideanSpace ℂ I) :
    unitarySphereCentered W (fun w => a w+b w) ψ=
      unitarySphereCentered W a ψ+unitarySphereCentered W b ψ := by
  have hk : unitaryWeightedRankOne W (fun w => a w+b w) ψ.ofLp=
      unitaryWeightedRankOne W a ψ.ofLp+unitaryWeightedRankOne W b ψ.ofLp := by
    simp only [unitaryWeightedRankOne,Complex.ofReal_add,add_smul,Finset.sum_add_distrib,smul_add]
  unfold unitarySphereCentered unitarySphereConjugation
  rw [hk]
  simp only [Complex.ofReal_add,Finset.sum_add_distrib,add_div,add_smul,smul_add,
    rectangularEuclideanCLM,map_add]
  abel

/-- The exact finite low/high decomposition retains the low scalar mean; it is not discarded. -/
theorem unitarySphereCentered_low_high [Nonempty I]
    (W : K → Matrix I I ℂ) (a : K → ℝ) (F : Finset K) (ψ : EuclideanSpace ℂ I) :
    unitarySphereCentered W a ψ=
      rectangularEuclideanCLM
        (unitaryOrbitMatrix (fun w : F => W w.val) ψ*
          Matrix.diagonal (fun w : F => (a w.val:ℂ))*(unitaryOrbitMatrix (fun w : F => W w.val) ψ)ᴴ)+
      unitarySphereCentered W (fun w => if w∈F then 0 else a w) ψ-
      rectangularEuclideanCLM (((∑ w∈F,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ)) := by
  have ha : a=(fun w => (if w∈F then a w else 0)+(if w∈F then 0 else a w)) := by
    funext w
    by_cases hw : w∈F <;> simp [hw]
  conv_lhs => rw [ha,unitarySphereCentered_add]
  unfold unitarySphereCentered
  rw [unitarySphereConjugation_finset]
  have hs : (∑ w,((if w∈F then a w else 0:ℝ):ℂ))=∑ w∈F,(a w:ℂ) := by
    simp only [apply_ite Complex.ofReal,Complex.ofReal_zero]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [hs]
  abel

omit [Fintype K] [DecidableEq K] in
/-- The exact low scalar center has its true normalized finite weight mass as a norm bound. -/
theorem orbitLowMean_norm_le (a : K → ℝ) (F : Finset K) :
    ‖rectangularEuclideanCLM (((∑ w∈F,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ))‖≤
      |(∑ w∈F,a w)/(Fintype.card I:ℝ)| := by
  have hc : (∑ w∈F,(a w:ℂ))=∑ w : F,(a w.val:ℂ) :=
    Finset.sum_subtype F (fun _ => Iff.rfl) (fun w => (a w:ℂ))
  have hr : (∑ w∈F,a w)=∑ w : F,a w.val :=
    Finset.sum_subtype F (fun _ => Iff.rfl) a
  have h := unitary_weight_mean_norm_le (I:=I) (fun w : F => a w.val)
  rw [← hc,← hr] at h
  exact h

omit [Fintype K] in
/-- The diagonal norm bound is the actual maximum coefficient bound on the low labels. -/
theorem orbitLowDiagonal_norm_le (a : K → ℝ) (F : Finset K) (M : ℝ) (hM : 0≤M)
    (ha : ∀ w∈F,|a w|≤M) :
    ‖Matrix.diagonal (fun w : F => (a w.val:ℂ))‖≤M := by
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro w
  simpa only [Complex.norm_real,Real.norm_eq_abs] using ha w.val w.property

/-- On one actual low Gram good event, the full centered operator is close to the canonical polar low compression. -/
theorem unitarySphereCentered_polar_approx [Nonempty I]
    (W : K → Matrix I I ℂ) (a : K → ℝ) (F : Finset K) (ψ : EuclideanSpace ℂ I)
    (t eps M : ℝ) (ht : t<1) (hM : 0≤M) (ha : ∀ w∈F,|a w|≤M)
    (hg : ‖(unitaryOrbitMatrix (fun w : F => W w.val) ψ)ᴴ*
      unitaryOrbitMatrix (fun w : F => W w.val) ψ-1‖≤t)
    (hh : ‖unitarySphereCentered W (fun w => if w∈F then 0 else a w) ψ‖≤eps) :
    let V := unitaryOrbitMatrix (fun w : F => W w.val) ψ
    let Q := matrixPolarCorrection V
    let A := Matrix.diagonal (fun w : F => (a w.val:ℂ))
    ‖unitarySphereCentered W a ψ-rectangularEuclideanCLM (Q*A*Qᴴ)‖≤
      3*M*t+eps+|(∑ w∈F,a w)/(Fintype.card I:ℝ)| := by
  dsimp only
  let V := unitaryOrbitMatrix (fun w : F => W w.val) ψ
  let Q := matrixPolarCorrection V
  let A := Matrix.diagonal (fun w : F => (a w.val:ℂ))
  let H := unitarySphereCentered W (fun w => if w∈F then 0 else a w) ψ
  let L := rectangularEuclideanCLM (((∑ w∈F,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ))
  have he : unitarySphereCentered W a ψ-rectangularEuclideanCLM (Q*A*Qᴴ)=
      rectangularEuclideanCLM (V*A*Vᴴ-Q*A*Qᴴ)+H-L := by
    rw [unitarySphereCentered_low_high W a F ψ]
    have hsub (B C : Matrix I I ℂ) :
        rectangularEuclideanCLM (B-C)=rectangularEuclideanCLM B-rectangularEuclideanCLM C := by
      simp only [rectangularEuclideanCLM,map_sub]
    rw [hsub]
    dsimp [V,A,H,L]
    abel
  rw [he]
  have ht0 : 0≤t := (norm_nonneg _).trans hg
  have hp : ‖rectangularEuclideanCLM (V*A*Vᴴ-Q*A*Qᴴ)‖≤3*M*t := by
    rw [rectangularEuclideanCLM_norm]
    exact (matrixPolarCorrection_conjugation_le V A ht hg).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (orbitLowDiagonal_norm_le a F M hM ha) (by norm_num)) ht0)
  exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    (add_le_add (add_le_add hp hh) (orbitLowMean_norm_le (I:=I) a F)))

end CertificationGaussian
