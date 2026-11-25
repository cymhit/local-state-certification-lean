import CertificationGaussian.MeasurableFrameRadial

/-! # Uniform operator control of the sphere energy

The exact centered-projector norm gives the off-net error in operator norm.
Joint continuity also makes a common sublevel event closed for an arbitrary,
possibly uncountable, family of operators. No countable-union assertion is
needed for that event, and no probability bound is asserted here.
-/

noncomputable section
open MeasureTheory Metric
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem unitCenteredProjectorHS_norm_sq (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    ‖unitCenteredProjectorHS (I := I) ψ‖^2 = 1-(Fintype.card I:ℝ)⁻¹ := by
  have hu : ‖(ψ : EuclideanSpace ℂ I)‖ = 1 := mem_sphere_zero_iff_norm.mp ψ.property
  have hD : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let P := matrixHilbertSchmidt (vectorRankOne (ψ : EuclideanSpace ℂ I) ψ)
  let J := matrixHilbertSchmidt (1 : Matrix I I ℂ)
  have hPP : inner ℝ P P = 1 := by
    rw [real_inner_self_eq_norm_sq, matrixHilbertSchmidt_norm_sq _ (vectorRankOne_self_hermitian _),
      vectorRankOne_self_sq _ hu, vectorRankOne_self_trace _ hu, Complex.one_re]
  have hJP : inner ℝ J P = 1 := by
    rw [matrixHilbertSchmidt_inner _ _ Matrix.isHermitian_one, one_mul,
      vectorRankOne_self_trace _ hu, Complex.one_re]
  have hPJ : inner ℝ P J = 1 := by rw [real_inner_comm]; exact hJP
  have hJJ : inner ℝ J J = (Fintype.card I:ℝ) := by
    rw [matrixHilbertSchmidt_inner _ _ Matrix.isHermitian_one, one_mul, Matrix.trace_one, Complex.natCast_re]
  change ‖P - (Fintype.card I:ℝ)⁻¹ • J‖^2 = _
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hPP, hJP, hPJ, hJJ]
  field_simp
  ring

theorem unitCenteredProjectorHS_norm_le_one (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    ‖unitCenteredProjectorHS (I := I) ψ‖ ≤ 1 := by
  have h := unitCenteredProjectorHS_norm_sq ψ
  have hD : 0 ≤ (Fintype.card I:ℝ)⁻¹ := by positivity
  nlinarith [norm_nonneg (unitCenteredProjectorHS (I := I) ψ)]

/-- The off-net bound depends only on the actual operator difference. -/
theorem gaussianFrameSphereScore_dist_le
    (T S : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I))
    (ψ : sphere (0 : EuclideanSpace ℂ I) 1) :
    |gaussianFrameSphereScore T ψ-gaussianFrameSphereScore S ψ| ≤
      (Fintype.card I:ℝ)^2 * ‖T-S‖ := by
  let X : EuclideanSpace ℂ (I × I) := unitCenteredProjectorHS (I := I) ψ
  have hX : ‖X‖^2 ≤ 1 := by
    rw [unitCenteredProjectorHS_norm_sq ψ]
    have hD : 0 ≤ (Fintype.card I:ℝ)⁻¹ := by positivity
    linarith
  have hi : |inner ℝ X ((T-S) X)| ≤ ‖T-S‖ := by
    calc
      _ = ‖inner ℝ X ((T-S) X)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖X‖ * ‖(T-S) X‖ := norm_inner_le_norm _ _
      _ ≤ ‖X‖ * (‖T-S‖ * ‖X‖) := mul_le_mul_of_nonneg_left ((T-S).le_opNorm _) (norm_nonneg _)
      _ = ‖T-S‖ * ‖X‖^2 := by ring
      _ ≤ ‖T-S‖ * 1 := mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      _ = _ := mul_one _
  have he : gaussianFrameSphereScore T ψ-gaussianFrameSphereScore S ψ =
      (Fintype.card I:ℝ)^2 * inner ℝ X ((T-S) X) := by
    change (Fintype.card I:ℝ)^2 * inner ℝ X (T X) -
      (Fintype.card I:ℝ)^2 * inner ℝ X (S X) = _
    simp only [sub_apply, inner_sub_right, mul_sub]
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left hi (sq_nonneg _)

omit [Nonempty I] in
@[fun_prop] theorem unitCenteredProjectorHS_continuous :
    Continuous (unitCenteredProjectorHS (I := I)) := by
  unfold unitCenteredProjectorHS matrixHilbertSchmidt vectorRankOne
  fun_prop

omit [Nonempty I] in
theorem gaussianFrameSphereScore_joint_continuous : Continuous (fun p :
    (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)) ×
      sphere (0 : EuclideanSpace ℂ I) 1 => gaussianFrameSphereScore p.1 p.2) := by
  change Continuous (fun p :
      (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)) ×
        sphere (0 : EuclideanSpace ℂ I) 1 =>
      (Fintype.card I:ℝ)^2 * inner ℝ (unitCenteredProjectorHS (I := I) p.2)
        (p.1 (unitCenteredProjectorHS (I := I) p.2)))
  fun_prop

omit [Nonempty I] in
/-- A common event for any operator family is an arbitrary intersection of
closed sets, hence measurable without a separability assumption on the family. -/
theorem isClosed_gaussianFrameSphereScore_uniform_sublevel
    (𝒯 : Set (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I))) (c : ℝ) :
    IsClosed {ψ : sphere (0 : EuclideanSpace ℂ I) 1 | ∀ T ∈ 𝒯, gaussianFrameSphereScore T ψ ≤ c} := by
  have hc (T : EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I)) :
      Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 => gaussianFrameSphereScore T ψ) := by
    change Continuous (fun ψ : sphere (0 : EuclideanSpace ℂ I) 1 =>
      (Fintype.card I:ℝ)^2 * inner ℝ (unitCenteredProjectorHS (I := I) ψ)
        (T (unitCenteredProjectorHS (I := I) ψ)))
    fun_prop
  have hclosed := isClosed_iInter (fun T => isClosed_iInter (fun (_ : T ∈ 𝒯) =>
    isClosed_le (hc T) (continuous_const : Continuous (fun _ : sphere (0 : EuclideanSpace ℂ I) 1 => c))))
  have he : {ψ : sphere (0 : EuclideanSpace ℂ I) 1 | ∀ T ∈ 𝒯, gaussianFrameSphereScore T ψ ≤ c} =
      ⋂ T, ⋂ (_ : T ∈ 𝒯), {ψ : sphere (0 : EuclideanSpace ℂ I) 1 | gaussianFrameSphereScore T ψ ≤ c} := by
    ext ψ
    constructor
    · intro h
      exact Set.mem_iInter.mpr (fun T => Set.mem_iInter.mpr (fun hT => h T hT))
    · intro h T hT
      exact Set.mem_iInter.mp (Set.mem_iInter.mp h T) hT
  rw [he]
  exact hclosed

omit [Nonempty I] in
theorem measurableSet_gaussianFrameSphereScore_uniform_sublevel
    (𝒯 : Set (EuclideanSpace ℂ (I × I) →L[ℝ] EuclideanSpace ℂ (I × I))) (c : ℝ) :
    MeasurableSet {ψ : sphere (0 : EuclideanSpace ℂ I) 1 | ∀ T ∈ 𝒯, gaussianFrameSphereScore T ψ ≤ c} :=
  (isClosed_gaussianFrameSphereScore_uniform_sublevel 𝒯 c).measurableSet

end CertificationGaussian
