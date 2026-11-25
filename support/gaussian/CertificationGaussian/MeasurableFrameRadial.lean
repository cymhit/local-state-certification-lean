import CertificationGaussian.MeasurableGaussianFrameBound
import CertificationGaussian.RadialProjection

/-! # Exact radial projection of a Hilbert--Schmidt frame

The Gaussian and sphere observables use the same vector and radius. Symmetry
and preservation of the identity make the two cross terms vanish exactly.
These operator identities are stable under the compact-closure construction.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Metric
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
private theorem hs_sub (A B : Matrix I I ℂ) :
    matrixHilbertSchmidt (A-B) = matrixHilbertSchmidt A - matrixHilbertSchmidt B := rfl

omit [Fintype I] [DecidableEq I] in
private theorem hs_real_smul (r : ℝ) (A : Matrix I I ℂ) :
    matrixHilbertSchmidt (r • A) = r • matrixHilbertSchmidt A := rfl

omit [Fintype I] [DecidableEq I] in
private theorem rankOne_real_smul (r : ℝ) (z : EuclideanSpace ℂ I) :
    vectorRankOne (r • z) (r • z) = r^2 • vectorRankOne z z := by
  ext i j
  simp only [vectorRankOne, PiLp.smul_apply, Complex.real_smul, star_mul,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_apply, Complex.ofReal_pow]
  ring

private theorem identity_hs_inner :
    inner ℝ (matrixHilbertSchmidt (1 : Matrix I I ℂ)) (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      (Fintype.card I : ℝ) := by
  rw [matrixHilbertSchmidt_inner _ _ Matrix.isHermitian_one, one_mul, Matrix.trace_one,
    Complex.natCast_re]

/-- The centered pure-state projector in the actual real HS space. -/
def unitCenteredProjectorHS (ψ : EuclideanSpace ℂ I) : EuclideanSpace ℂ (I × I) :=
  matrixHilbertSchmidt (vectorRankOne ψ ψ) -
    (Fintype.card I : ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix I I ℂ)

/-- The sphere quadratic energy of an actual HS operator. -/
def gaussianFrameSphereScore
    (T : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I))
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) : ℝ :=
  (Fintype.card I : ℝ)^2 * inner ℝ (unitCenteredProjectorHS ψ) (T (unitCenteredProjectorHS ψ))

variable [Nonempty I]

theorem unitCenteredProjectorHS_orthogonal_identity (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    inner ℝ (matrixHilbertSchmidt (1 : Matrix I I ℂ)) (unitCenteredProjectorHS ψ) = 0 := by
  have hD : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [unitCenteredProjectorHS, inner_sub_right, real_inner_smul_right,
    matrixHilbertSchmidt_inner _ _ Matrix.isHermitian_one, one_mul,
    vectorRankOne_self_trace _ (mem_sphere_zero_iff_norm.mp ψ.property), Complex.one_re,
    identity_hs_inner, inv_mul_cancel₀ hD, sub_self]

omit [Nonempty I] [DecidableEq I] in
private theorem rankOne_direction (e₀ : sphere (0 : EuclideanSpace ℂ I) 1)
    (z : EuclideanSpace ℂ I) (hz : z ≠ 0) :
    vectorRankOne z z = ‖z‖^2 • vectorRankOne (sphereDirection e₀ z) (sphereDirection e₀ z) := by
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have he : ‖z‖ • (sphereDirection e₀ z : EuclideanSpace ℂ I) = z := by
    rw [sphereDirection_coe, ite_eq_right hz, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  calc
    _ = vectorRankOne (‖z‖ • (sphereDirection e₀ z : EuclideanSpace ℂ I))
        (‖z‖ • (sphereDirection e₀ z : EuclideanSpace ℂ I)) := by rw [he]
    _ = _ := rankOne_real_smul _ _

/-- Decompose the same Gaussian projector into its traceless direction and radius. -/
theorem gaussianCenteredProjector_radial_decomposition
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : Fin 2 × I → ℝ)
    (hx : complexGaussianLift I x ≠ 0) :
    matrixHilbertSchmidt (gaussianCenteredProjector x) =
      ((Fintype.card I : ℝ) * gaussianRadius I x) •
        unitCenteredProjectorHS (sphereDirection e₀ (complexGaussianLift I x)) +
      (gaussianRadius I x-1) • matrixHilbertSchmidt (1 : Matrix I I ℂ) := by
  have hD : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : ‖complexGaussianLift I x‖^2 = (Fintype.card I : ℝ)*gaussianRadius I x := by
    rw [gaussianRadius_eq_norm_sq]
    field_simp
  have hc : ((Fintype.card I : ℝ)*gaussianRadius I x) * (Fintype.card I : ℝ)⁻¹ = gaussianRadius I x := by
    field_simp
  change matrixHilbertSchmidt (vectorRankOne (complexGaussianLift I x) (complexGaussianLift I x)-1) = _
  rw [hs_sub, rankOne_direction e₀ _ hx, hs_real_smul, hn, unitCenteredProjectorHS,
    smul_sub, smul_smul, hc]
  module

/-- Exact same-sample radial identity, including the rank-one radius-zero kernel. -/
theorem gaussianFrame_radial_identity
    (T : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I))
    (hT : ∀ A B, inner ℝ A (T B) = inner ℝ (T A) B)
    (hI : T (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      (Fintype.card I : ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix I I ℂ))
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : Fin 2 × I → ℝ)
    (hx : complexGaussianLift I x ≠ 0) :
    gaussianFrameSphereScore T (sphereDirection e₀ (complexGaussianLift I x)) =
      (inner ℝ (matrixHilbertSchmidt (gaussianCenteredProjector x))
        (T (matrixHilbertSchmidt (gaussianCenteredProjector x))) - (gaussianRadius I x-1)^2) /
        (gaussianRadius I x)^2 := by
  let X : EuclideanSpace ℂ (I × I) := unitCenteredProjectorHS (I := I)
    (sphereDirection e₀ (complexGaussianLift I x))
  let J := matrixHilbertSchmidt (1 : Matrix I I ℂ)
  have hD : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJX : inner ℝ J X = 0 := unitCenteredProjectorHS_orthogonal_identity _
  have hXJ : inner ℝ X (T J) = 0 := by
    change inner ℝ X (T (matrixHilbertSchmidt (1 : Matrix I I ℂ))) = 0
    rw [hI, real_inner_smul_right, real_inner_comm, hJX, mul_zero]
  have hJTX : inner ℝ J (T X) = 0 := by
    rw [hT]
    change inner ℝ (T (matrixHilbertSchmidt (1 : Matrix I I ℂ))) X = 0
    rw [hI, real_inner_smul_left, hJX, mul_zero]
  have hJTJ : inner ℝ J (T J) = 1 := by
    change inner ℝ (matrixHilbertSchmidt (1 : Matrix I I ℂ))
      (T (matrixHilbertSchmidt (1 : Matrix I I ℂ))) = 1
    rw [hI, real_inner_smul_right, identity_hs_inner, inv_mul_cancel₀ hD]
  have ht : gaussianRadius I x ≠ 0 := (gaussianRadius_pos_of_nonzero x hx).ne'
  apply (eq_div_iff (pow_ne_zero 2 ht)).2
  rw [gaussianCenteredProjector_radial_decomposition e₀ x hx]
  change (Fintype.card I : ℝ)^2 * inner ℝ X (T X) * (gaussianRadius I x)^2 =
    inner ℝ (((Fintype.card I : ℝ)*gaussianRadius I x) • X + (gaussianRadius I x-1) • J)
      (T (((Fintype.card I : ℝ)*gaussianRadius I x) • X + (gaussianRadius I x-1) • J)) -
        (gaussianRadius I x-1)^2
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hXJ, hJTX, hJTJ, mul_zero, mul_one, add_zero, zero_add]
  ring

private def matrixHSRealMap : Matrix I I ℂ →L[ℝ] EuclideanSpace ℂ (I × I) :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixHilbertSchmidt
      map_add' := by intro A B; rfl
      map_smul' := by intro r A; rfl }

section ActualFrame
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
  (B : Ω → Matrix I I ℂ) (hB : AEStronglyMeasurable B ν)
  {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ s ∂ν, ‖matrixHilbertSchmidt (B s)‖ ≤ K)
include hB hK hbound

omit [Nonempty I] [DecidableEq I] in
theorem integralMatrixFrame_symmetric (X Y : EuclideanSpace ℂ (I × I)) :
    inner ℝ X (integralMatrixFrame ν B Y) = inner ℝ (integralMatrixFrame ν B X) Y := by
  have hV : AEStronglyMeasurable (fun s => matrixHilbertSchmidt (B s)) ν :=
    matrixHSRealMap.continuous.comp_aestronglyMeasurable hB
  rw [real_inner_comm, integralMatrixFrame,
    integralHilbertFrame_inner ν _ hV hK hbound,
    integralHilbertFrame_inner ν _ hV hK hbound]
  apply integral_congr_ae
  exact ae_of_all _ fun s => mul_comm _ _

omit [Nonempty I] in
/-- The identity constraint is derived from the actual trace-one ensemble and
its matrix mean; it is not an uninstantiated property of the frame. -/
theorem integralMatrixFrame_identity
    (hH : ∀ᵐ s ∂ν, (B s).IsHermitian) (htrace : ∀ᵐ s ∂ν, (B s).trace = 1)
    (hmean : (∫ s, B s ∂ν) = (Fintype.card I : ℝ)⁻¹ • (1 : Matrix I I ℂ)) :
    integralMatrixFrame ν B (matrixHilbertSchmidt (1 : Matrix I I ℂ)) =
      (Fintype.card I : ℝ)⁻¹ • matrixHilbertSchmidt (1 : Matrix I I ℂ) := by
  have hV : AEStronglyMeasurable (fun s => matrixHilbertSchmidt (B s)) ν :=
    matrixHSRealMap.continuous.comp_aestronglyMeasurable hB
  have hF := integralHilbertFrame_integrable ν _ hV hK hbound
  have hBi : Integrable B ν := measurableMatrix_continuous_integrable ν B hB hbound id continuous_id
  rw [integralMatrixFrame, integralHilbertFrame, ContinuousLinearMap.integral_apply hF]
  calc
    _ = ∫ s, matrixHilbertSchmidt (B s) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hH, htrace] with s hs ht
      rw [InnerProductSpace.rankOne_apply, matrixHilbertSchmidt_inner _ _ hs, mul_one, ht,
        Complex.one_re, one_smul]
    _ = matrixHSRealMap (∫ s, B s ∂ν) := (matrixHSRealMap.integral_comp_comm hBi)
    _ = _ := by rw [hmean, map_smul]; rfl

/-- The operator energy equals the genuine reference integral of the normalized
sphere quadratic form for the same trace-one measurable ensemble. -/
theorem gaussianFrameSphereScore_eq_integral
    (hH : ∀ᵐ s ∂ν, (B s).IsHermitian) (htrace : ∀ᵐ s ∂ν, (B s).trace = 1)
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    gaussianFrameSphereScore (integralMatrixFrame ν B) ψ =
      ∫ s, ((Fintype.card I : ℝ)*(sphereQuadraticForm (B s) ψ).re - 1)^2 ∂ν := by
  have hD : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hV : AEStronglyMeasurable (fun s => matrixHilbertSchmidt (B s)) ν :=
    matrixHSRealMap.continuous.comp_aestronglyMeasurable hB
  rw [gaussianFrameSphereScore, real_inner_comm, integralMatrixFrame,
    integralHilbertFrame_inner ν _ hV hK hbound, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hH, htrace] with s hs ht
  have he : inner ℝ (matrixHilbertSchmidt (B s)) (unitCenteredProjectorHS (I := I) ψ) =
      (sphereQuadraticForm (B s) ψ).re - (Fintype.card I : ℝ)⁻¹ := by
    rw [unitCenteredProjectorHS, inner_sub_right, real_inner_smul_right,
      matrixHilbertSchmidt_inner _ _ hs, matrixHilbertSchmidt_inner _ _ hs,
      vectorRankOne_trace_pairing, mul_one, ht, Complex.one_re, mul_one]
  rw [he]
  field_simp

/-- The original ensemble, its exact frame and the same original Gaussian all
occur in this concrete radial identity. -/
theorem measurableQuadraticEnsemble_radial_identity
    (hH : ∀ᵐ s ∂ν, (B s).IsHermitian) (htrace : ∀ᵐ s ∂ν, (B s).trace = 1)
    (hmean : (∫ s, B s ∂ν) = (Fintype.card I : ℝ)⁻¹ • (1 : Matrix I I ℂ))
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : Fin 2 × I → ℝ)
    (hx : complexGaussianLift I x ≠ 0) :
    gaussianFrameSphereScore (integralMatrixFrame ν B) (sphereDirection e₀ (complexGaussianLift I x)) =
      (measurableQuadraticEnsemble ν B x - (gaussianRadius I x-1)^2)/(gaussianRadius I x)^2 := by
  rw [gaussianFrame_radial_identity _ (integralMatrixFrame_symmetric ν B hB hK hbound)
    (integralMatrixFrame_identity ν B hB hK hbound hH htrace hmean) e₀ x hx,
    measurableQuadraticEnsemble_eq_frame ν B hB hH hK hbound]
  rfl

end ActualFrame
end CertificationGaussian
