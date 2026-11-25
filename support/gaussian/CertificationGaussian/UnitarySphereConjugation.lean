import CertificationGaussian.RadialHighGaussian
import CertificationGaussian.ReadoutRadialControl

noncomputable section
open MeasureTheory Matrix Metric
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- On a normalized vector the paper's operator is D times the existing 1/D Gaussian rank-one sum. -/
def unitarySphereConjugation (W : K → Matrix I I ℂ) (a : K → ℝ)
    (ψ : EuclideanSpace ℂ I) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  rectangularEuclideanCLM ((Fintype.card I:ℂ) • unitaryWeightedRankOne W a ψ.ofLp)

/-- The same proved Gaussian centering scalar is retained after normalization. -/
def unitarySphereCentered (W : K → Matrix I I ℂ) (a : K → ℝ)
    (ψ : EuclideanSpace ℂ I) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  unitarySphereConjugation W a ψ-
    rectangularEuclideanCLM (((∑ w,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ))

omit [DecidableEq K] in
/-- This is the actual unnormalized sum of weighted unitary orbit projectors on the normalized input. -/
theorem unitarySphereConjugation_eq_sum [Nonempty I] (W : K → Matrix I I ℂ) (a : K → ℝ)
    (ψ : EuclideanSpace ℂ I) :
    unitarySphereConjugation W a ψ=rectangularEuclideanCLM
      (∑ w,(a w:ℂ) • (W w*Matrix.vecMulVec ψ.ofLp (fun i => star (ψ.ofLp i))*(W w)ᴴ)) := by
  have hD : (Fintype.card I:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  unfold unitarySphereConjugation unitaryWeightedRankOne
  rw [smul_smul,mul_inv_cancel₀ hD,one_smul]

omit [DecidableEq I] [DecidableEq K] in
/-- Rescaling the vector by a real scalar multiplies the weighted rank-one matrix by its square. -/
theorem unitaryWeightedRankOne_real_smul (W : K → Matrix I I ℂ) (a : K → ℝ)
    (c : ℝ) (z : I → ℂ) :
    unitaryWeightedRankOne W a (fun i => c • z i)=(c:ℂ)^2 • unitaryWeightedRankOne W a z := by
  have hp : Matrix.vecMulVec (fun i => c • z i) (fun i => star (c • z i))=
      (c:ℂ)^2 • Matrix.vecMulVec z (fun i => star (z i)) := by
    ext i j
    simp only [Matrix.vecMulVec_apply,Matrix.smul_apply,Complex.real_smul,smul_eq_mul,
      star_mul,Complex.star_def,Complex.conj_ofReal]
    ring
  unfold unitaryWeightedRankOne
  rw [hp]
  have hs : (∑ w,(a w:ℂ) •
      (W w*((c:ℂ)^2 • Matrix.vecMulVec z (fun i => star (z i)))*(W w)ᴴ))=
      (c:ℂ)^2 • ∑ w,(a w:ℂ) •
        (W w*Matrix.vecMulVec z (fun i => star (z i))*(W w)ᴴ) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [Matrix.mul_smul,Matrix.smul_mul]
    exact smul_comm _ _ _
  rw [hs]
  exact smul_comm _ _ _

omit [DecidableEq K] in
@[fun_prop] theorem unitarySphereConjugation_continuous (W : K → Matrix I I ℂ) (a : K → ℝ) :
    Continuous (unitarySphereConjugation W a) := by
  have he : unitarySphereConjugation W a=(fun ψ : EuclideanSpace ℂ I =>
      (Fintype.card I:ℂ) • rectangularEuclideanCLM
        (matrixSesquilinear (unitaryChaosCoefficient W a) ψ.ofLp ψ.ofLp)) := by
    funext ψ
    unfold unitarySphereConjugation
    rw [← matrixSesquilinear_unitaryChaosCoefficient]
    simp only [rectangularEuclideanCLM,map_smul]
  rw [he]
  simp only [rectangularEuclideanCLM,matrixSesquilinear,map_sum,map_smul]
  fun_prop

omit [DecidableEq K] in
@[fun_prop] theorem unitarySphereCentered_continuous (W : K → Matrix I I ℂ) (a : K → ℝ) :
    Continuous (unitarySphereCentered W a) :=
  (unitarySphereConjugation_continuous W a).sub continuous_const

omit [DecidableEq K] in
/-- Exact transport of the same Gaussian rank-one operator along the actual sphereDirection, away from the origin. -/
theorem unitarySphereConjugation_direction (W : K → Matrix I I ℂ) (a : K → ℝ)
    (z : I → ℂ) (hz : (WithLp.toLp 2 z : EuclideanSpace ℂ I)≠0)
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    unitarySphereConjugation W a (sphereDirection e₀ (WithLp.toLp 2 z))=
      (readoutRadialAlpha (Fintype.card I:ℝ) z:ℂ) • rectangularEuclideanCLM (unitaryWeightedRankOne W a z) := by
  have hd : (sphereDirection e₀ (WithLp.toLp 2 z) : EuclideanSpace ℂ I).ofLp=
      (fun i => ‖(WithLp.toLp 2 z : EuclideanSpace ℂ I)‖⁻¹ • z i) := by
    funext i
    rw [sphereDirection_coe]
    simp only [hz,ite_false]
    rfl
  unfold unitarySphereConjugation
  rw [hd,unitaryWeightedRankOne_real_smul,smul_smul]
  have hc : (Fintype.card I:ℂ)*((‖(WithLp.toLp 2 z : EuclideanSpace ℂ I)‖⁻¹:ℝ):ℂ)^2=
      (readoutRadialAlpha (Fintype.card I:ℝ) z:ℂ) := by
    simp [readoutRadialAlpha,inv_pow,div_eq_mul_inv]
  rw [hc]
  simp only [rectangularEuclideanCLM,map_smul]

omit [DecidableEq K] in
/-- Centering produces precisely the additional (alpha-1)*sigma I term, not a second independent radius. -/
theorem unitarySphereCentered_direction (W : K → Matrix I I ℂ) (a : K → ℝ)
    (x : Fin 2 × I → ℝ) (hx : complexGaussianLift I x≠0)
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    unitarySphereCentered W a (sphereDirection e₀ (complexGaussianLift I x))=
      (readoutRadialAlpha (Fintype.card I:ℝ) (complexCoordinate x):ℂ) • unitaryGaussianCentered W a x+
      ((readoutRadialAlpha (Fintype.card I:ℝ) (complexCoordinate x)-1:ℝ):ℂ) •
        rectangularEuclideanCLM (((∑ w,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ)) := by
  unfold unitarySphereCentered unitaryGaussianCentered unitaryGaussianConjugation
  simp only [complexGaussianLift] at hx ⊢
  rw [unitarySphereConjugation_direction W a (complexCoordinate x) hx e₀]
  have hc : ((readoutRadialAlpha (Fintype.card I:ℝ) (complexCoordinate x)-1:ℝ):ℂ)=
      (readoutRadialAlpha (Fintype.card I:ℝ) (complexCoordinate x):ℂ)-(1:ℂ) := by push_cast; rfl
  rw [hc]
  ext y i
  simp only [_root_.sub_apply,_root_.add_apply,_root_.smul_apply,
    PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

omit [DecidableEq K] in
/-- The actual scalar mean matrix has norm at most the absolute real weight mean, including an empty index. -/
theorem unitary_weight_mean_norm_le (a : K → ℝ) :
    ‖rectangularEuclideanCLM (((∑ w,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ))‖≤
      |(∑ w,a w)/(Fintype.card I:ℝ)| := by
  have hc : ((∑ w,(a w:ℂ))/(Fintype.card I:ℂ))=
      (((∑ w,a w)/(Fintype.card I:ℝ):ℝ):ℂ) := by push_cast; rfl
  have hI : ‖(1:Matrix I I ℂ)‖≤1 := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
      unitary_matrix_norm_le_one (1:Matrix I I ℂ) (by simp)
  rw [rectangularEuclideanCLM_norm,hc,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hI (abs_nonneg ((∑ w,a w)/(Fintype.card I:ℝ)))

omit [DecidableEq K] in
/-- Deterministic bound for the genuinely normalized high operator in terms of the same Gaussian error and same common radius. -/
theorem unitarySphereCentered_direction_norm_le (W : K → Matrix I I ℂ) (a : K → ℝ)
    (x : Fin 2 × I → ℝ) (hx : complexGaussianLift I x≠0)
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) :
    ‖unitarySphereCentered W a (sphereDirection e₀ (complexGaussianLift I x))‖≤
      |readoutRadialAlpha (Fintype.card I:ℝ) (complexCoordinate x)| *‖unitaryGaussianCentered W a x‖+
      |readoutRadialAlpha (Fintype.card I:ℝ) (complexCoordinate x)-1| *
        |(∑ w,a w)/(Fintype.card I:ℝ)| := by
  rw [unitarySphereCentered_direction W a x hx e₀]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (unitary_weight_mean_norm_le (I:=I) a) (abs_nonneg _))

end CertificationGaussian
