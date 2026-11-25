import CertificationGaussian.RadialHighChoi
import CertificationGaussian.UnitaryGaussianChaos

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

section Centered
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Weighted Gaussian conjugation centered by its scalar mean operator. -/
def unitaryGaussianCentered (W : K → Matrix I I ℂ) (a : K → ℝ)
    (x : Fin 2 × I → ℝ) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  unitaryGaussianConjugation W a x-
    rectangularEuclideanCLM (((∑ w,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ))

omit [DecidableEq K] in
theorem unitaryGaussianCentered_integrable (W : K → Matrix I I ℂ) (a : K → ℝ) :
    Integrable (unitaryGaussianCentered W a) (pairedGaussian I) := by
  let : IsProbabilityMeasure (pairedGaussian I) := by unfold pairedGaussian; infer_instance
  exact (unitaryGaussianConjugation_integrable W a).sub (integrable_const _)

omit [DecidableEq K] in
@[fun_prop] theorem unitaryGaussianCentered_continuous (W : K → Matrix I I ℂ) (a : K → ℝ) :
    Continuous (unitaryGaussianCentered W a) := by
  unfold unitaryGaussianCentered
  apply Continuous.sub _ continuous_const
  have hq : Continuous (fun x : Fin 2 × I → ℝ =>
      complexGaussianQuadratic (unitaryChaosCoefficient W a) x) := by
    simp_rw [complexGaussianQuadratic_eq_sum]
    unfold complexCoordinate
    fun_prop
  convert hq using 1
  funext x
  exact unitaryGaussianConjugation_eq_quadratic W a x

omit [DecidableEq K] in
/-- A true operator-norm event for the same centered random operator is Borel. -/
theorem unitaryGaussianCentered_bad_measurable (W : K → Matrix I I ℂ) (a : K → ℝ) (t : ℝ) :
    MeasurableSet {x | t<‖unitaryGaussianCentered W a x‖} :=
  (isOpen_lt continuous_const (unitaryGaussianCentered_continuous W a).norm).measurableSet

omit [DecidableEq K] in
/-- Scalar multiplication of the real weights acts on the actual centered CLM-valued Gaussian operator. -/
theorem unitaryGaussianCentered_weight_smul (W : K → Matrix I I ℂ) (a : K → ℝ)
    (c : ℝ) (x : Fin 2 × I → ℝ) :
    unitaryGaussianCentered W (fun w => c*a w) x=(c:ℂ) • unitaryGaussianCentered W a x := by
  have hk : unitaryWeightedRankOne W (fun w => c*a w) (complexCoordinate x)=
      (c:ℂ) • unitaryWeightedRankOne W a (complexCoordinate x) := by
    unfold unitaryWeightedRankOne
    simp only [Complex.ofReal_mul,mul_smul,← Finset.smul_sum]
    exact smul_comm _ _ _
  have hmean : rectangularEuclideanCLM
      (((∑ w,((c*a w:ℝ):ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ))=
      (c:ℂ) • rectangularEuclideanCLM
        (((∑ w,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ)) := by
    simp only [Complex.ofReal_mul,← Finset.mul_sum,mul_div_assoc,mul_smul,
      rectangularEuclideanCLM,map_smul]
  unfold unitaryGaussianCentered unitaryGaussianConjugation
  rw [hk,hmean,smul_sub]
  simp only [rectangularEuclideanCLM,map_smul]

omit [DecidableEq K] in
/-- The centering in the definition is the genuine Gaussian mean when the coefficient family is unitary. -/
theorem unitaryGaussianCentered_mean_zero (W : K → Matrix I I ℂ) (a : K → ℝ)
    (hW : ∀ w,W w∈unitary (Matrix I I ℂ)) :
    (∫ x,unitaryGaussianCentered W a x∂pairedGaussian I)=0 := by
  let : IsProbabilityMeasure (pairedGaussian I) := by unfold pairedGaussian; infer_instance
  unfold unitaryGaussianCentered
  rw [integral_sub (unitaryGaussianConjugation_integrable W a) (integrable_const _),
    unitaryGaussianConjugation_mean W a hW]
  simp

end Centered

/-- Explicit fixed coefficient in the n^-11 first high Gaussian expectation estimate. -/
def radialHighGaussianConstant (d r : ℕ) (lam : ℕ → ℝ) : ℝ :=
  (8*gaussianMatrixChaosConstant)*(Real.log 2+Real.log (d:ℝ))*
    (Real.sqrt (radialCoefficientPolynomialConstant d r lam*complementLambdaCoefficient d r lam)+
      radialCoefficientPolynomialConstant d r lam+2)

theorem radialHighGaussianConstant_pos (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) :
    0<radialHighGaussianConstant d r lam := by
  have hB := radialCoefficientPolynomialConstant_nonneg d r lam
  have hg := gaussianMatrixChaosConstant_pos
  have hdlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  have htwo : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  unfold radialHighGaussianConstant
  positivity

/-- The physical matrix dimension contributes just a linear logarithmic factor. -/
theorem qudit_log_dimension_le (d n : ℕ) (hd : 1≤d) (hn : 1≤n) :
    Real.log (2*(Fintype.card (QuditIndex d n):ℝ))≤(Real.log 2+Real.log (d:ℝ))*(n:ℝ) := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have htwo : 0≤Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  rw [qudit_card,Nat.cast_pow,Real.log_mul (by norm_num) (pow_ne_zero _ hd0.ne'),Real.log_pow]
  nlinarith

/-- Both actual high coefficient controls are bounded by one explicit n^-12 factor. -/
theorem radialFirstHigh_scalar_controls {K : Type*} [Fintype K] [DecidableEq K]
    (d n r : ℕ) (hd : 1≤d) (hn : 1≤n) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    Real.sqrt (unitaryWeightSquareMean (I:=QuditIndex d n) (radialFirstHighWeights (S:=Fin n) d r lam k0)) ≤
      Real.sqrt (radialCoefficientPolynomialConstant d r lam*complementLambdaCoefficient d r lam)*((n:ℝ)^12)⁻¹ ∧
    ‖radialFirstHighWeights (S:=Fin n) d r lam k0‖≤
      radialCoefficientPolynomialConstant d r lam*((n:ℝ)^12)⁻¹ := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  constructor
  · simpa only [unitaryWeightSquareMean,qudit_card,Nat.cast_pow,Fintype.card_fin] using
      radialFirstHighWeights_sqrt_square_mass (S:=Fin n) d r hd (by simpa using hn) lam k0 hcard
  · have h := radialFirstHighWeights_norm_le (S:=Fin n) d r hd (by simpa using hn) lam k0
    simp only [Fintype.card_fin] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (radialCoefficientPolynomialConstant_nonneg d r lam))
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hn0 12)
      (pow_le_pow_right₀ hn1 (show 12≤r+24 by omega))

/-- Genuine first high-block Gaussian expectation, with a fixed constant and threshold uniform over all local HS unitary families. -/
theorem radialFirstHigh_gaussian_expectation {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      (∫ x,‖unitaryGaussianCentered
        (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialFirstHighWeights d r lam k0) x‖∂pairedGaussian (QuditIndex d n)) ≤
          radialHighGaussianConstant d r lam*((n:ℝ)^11)⁻¹ := by
  let : NeZero d := ⟨by omega⟩
  let B := radialCoefficientPolynomialConstant d r lam
  let A := complementLambdaCoefficient d r lam
  have hB : 0≤B := radialCoefficientPolynomialConstant_nonneg d r lam
  have hM : 0≤Real.sqrt (B*A)+B+2 := by positivity
  have hlog : 0≤Real.log 2+Real.log (d:ℝ) := by
    have h2 : 0≤Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
    have hd' : 0≤Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤d by omega))
    linarith
  filter_upwards [radialFirstHigh_bell_partialTranspose_eventually d r hd lam k0 hcard,
    eventually_ge_atTop 1] with n hPT hn
  intro W h0 hW hHS
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a := radialFirstHighWeights (S:=Fin n) d r lam k0
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp : 0≤((n:ℝ)^12)⁻¹ := by positivity
  have hg := unitaryGaussianConjugation_expectation_bound G a
    (radialTensorFamily_unitary d n W hW) (radialTensorFamily_hilbertSchmidt d n W hHS)
  have hs := radialFirstHigh_scalar_controls d n r (by omega) hn lam k0 hcard
  have ht : ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix G a))‖≤2*((n:ℝ)^12)⁻¹ := by
    simpa only [rectangularEuclideanCLM_norm,Matrix.l2_opNorm_toEuclideanCLM] using hPT W h0 hW hHS
  have hm : max (Real.sqrt (unitaryWeightSquareMean (I:=QuditIndex d n) a))
      (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix G a))‖) ≤
        (Real.sqrt (B*A)+B+2)*((n:ℝ)^12)⁻¹ := by
    refine max_le (hs.1.trans ?_) (max_le (hs.2.trans ?_) (ht.trans ?_))
    all_goals apply mul_le_mul_of_nonneg_right _ hp
    · dsimp [B,A]; linarith [radialCoefficientPolynomialConstant_nonneg d r lam]
    · linarith [Real.sqrt_nonneg (B*A)]
    · linarith [Real.sqrt_nonneg (B*A)]
  have hfactor : (8*gaussianMatrixChaosConstant)*Real.log (2*(Fintype.card (QuditIndex d n):ℝ))≤
      (8*gaussianMatrixChaosConstant)*((Real.log 2+Real.log (d:ℝ))*(n:ℝ)) :=
    mul_le_mul_of_nonneg_left (qudit_log_dimension_le d n (by omega) hn)
      (mul_nonneg (by norm_num) gaussianMatrixChaosConstant_pos.le)
  have hm0 : 0≤max (Real.sqrt (unitaryWeightSquareMean (I:=QuditIndex d n) a))
      (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix G a))‖) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hfactor0 : 0≤(8*gaussianMatrixChaosConstant)*((Real.log 2+Real.log (d:ℝ))*(n:ℝ)) := by
    exact mul_nonneg (mul_nonneg (by norm_num) gaussianMatrixChaosConstant_pos.le)
      (mul_nonneg hlog (Nat.cast_nonneg _))
  refine hg.trans ((mul_le_mul hfactor hm hm0 hfactor0).trans_eq ?_)
  change (8*gaussianMatrixChaosConstant)*((Real.log 2+Real.log (d:ℝ))*(n:ℝ))*
    ((Real.sqrt (B*A)+B+2)*((n:ℝ)^12)⁻¹) =
      (8*gaussianMatrixChaosConstant)*(Real.log 2+Real.log (d:ℝ))*(Real.sqrt (B*A)+B+2)*((n:ℝ)^11)⁻¹
  field_simp

/-- The actual second high block retains the exact factor2 and squared original coefficients. -/
theorem radialSecondHigh_gaussian_expectation {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      (∫ x,‖unitaryGaussianCentered
        (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialSecondHighWeights d r lam k0) x‖∂pairedGaussian (QuditIndex d n)) ≤
          (2*radialHighGaussianConstant d r (fun j => (lam j)^2))*((n:ℝ)^11)⁻¹ := by
  filter_upwards [radialFirstHigh_gaussian_expectation d r hd (fun j => (lam j)^2) k0 hcard] with n hn
  intro W h0 hW hHS
  have he : radialSecondHighWeights (S:=Fin n) d r lam k0=
      (fun w => 2*radialFirstHighWeights d r (fun j => (lam j)^2) k0 w) :=
    funext (radialSecondHighWeights_eq d r lam k0)
  simp only [he,unitaryGaussianCentered_weight_smul,norm_smul]
  rw [Complex.norm_of_nonneg (show (0:ℝ)≤2 by norm_num)]
  rw [integral_const_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hn W h0 hW hHS) (show (0:ℝ)≤2 by norm_num)

end CertificationGaussian
