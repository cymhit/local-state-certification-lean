import CertificationGaussian.CardinalityComplementRemainder

noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- Pointwise normal-order entry expansion on the actual real Gaussian coordinates. -/
theorem complexGaussianNormalMatrix_positions_eval {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (x : Fin 2 × I → ℝ) :
    complexGaussianNormalMatrix A B (complexCoordinate x) =
      ∑ a,∑ b,∑ c,∑ d,(A a c*B b d)*complexCoordinatePolyEval (gaussianNormalQuartic a b c d) x := by
  have h := gaussianNormalMatrixPolynomial_eval A B x
  simpa only [gaussianNormalMatrixPolynomial,complexCoordinatePolyEval,map_sum,map_mul,eval_C] using h.symm

section CompactRecord
variable {Ω I : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The actual matrix remainder is a finite polynomial in the original Gaussian coordinates with genuine averaged matrix coefficients. -/
theorem normalReadoutRemainder_polynomial_formula (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) (x : Fin 2 × I → ℝ) :
    normalReadoutRemainder μ D P H (complexCoordinate x) =
      D • ∑ a,∑ b,∑ c,∑ d,complexCoordinatePolyEval (gaussianNormalQuartic a b c d) x •
        (∫ ω,(H ω a c*H ω b d) • P ω∂μ) := by
  let K (a b c d : I) : Ω → Matrix I I ℂ := fun ω => (H ω a c*H ω b d) • P ω
  have hK (a b c d : I) : Continuous (K a b c d) := by dsimp [K]; fun_prop
  change _ = D • ∑ a,∑ b,∑ c,∑ d,complexCoordinatePolyEval (gaussianNormalQuartic a b c d) x •
    (∫ ω,K a b c d ω∂μ)
  have he : (fun ω => complexGaussianNormalMatrix (H ω) (H ω) (complexCoordinate x) • P ω) =
      (fun ω => ∑ a,∑ b,∑ c,∑ d,complexCoordinatePolyEval (gaussianNormalQuartic a b c d) x •
        K a b c d ω) := by
    funext ω
    rw [complexGaussianNormalMatrix_positions_eval]
    simp only [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    dsimp [K]
    rw [mul_comm,mul_smul]
  unfold normalReadoutRemainder
  rw [he]
  have hi (f : Ω → Matrix I I ℂ) (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp (disch := (intro _ _; apply hi; fun_prop)) only [integral_finsetSum,integral_smul]

omit [Fintype I] [DecidableEq I] in
@[fun_prop] theorem complexCoordinatePolyEval_continuous (P : MvPolynomial (Fin 2 × I) ℂ) :
    Continuous (complexCoordinatePolyEval P) := by
  unfold complexCoordinatePolyEval
  exact P.continuous_eval.comp (by fun_prop)

/-- The actual matrix-valued remainder is continuous in its Gaussian coordinates, not merely almost-everywhere defined. -/
@[fun_prop] theorem normalReadoutRemainder_gaussian_continuous (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) :
    Continuous (fun x => normalReadoutRemainder μ D P H (complexCoordinate x)) := by
  simp_rw [funext (normalReadoutRemainder_polynomial_formula μ D P H hP hH)]
  fun_prop

end CompactRecord

/-- The original finite-complement Z has a genuine continuous Euclidean operator-norm function. -/
@[fun_prop] theorem finiteComplementRemainder_opNorm_continuous
    {S K Ω : Type*} [Fintype S] [DecidableEq S] [Fintype K]
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω] (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (A : K → Finset S) (c : K → ℝ) :
    Continuous (fun x => ‖Matrix.toEuclideanCLM (n:=S → Fin d) (𝕜:=ℂ)
      (finiteComplementRemainder d μ record A c (complexCoordinate x))‖) := by
  have h := normalReadoutRemainder_gaussian_continuous (Measure.pi (fun _ : S => μ))
    ((d:ℝ)^(Fintype.card S)) (productRecordedProjector d record) (finiteComplementKernel d record A c)
    (productRecordedProjector_continuous d record hr) (finiteComplementKernel_continuous d record hr A c)
  simpa only [Matrix.l2_opNorm_toEuclideanCLM,finiteComplementRemainder] using h.norm

end CertificationGaussian
