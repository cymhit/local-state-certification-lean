import CertificationGaussian.ReadoutNormalization

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

section Quadratic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Additivity of the same actual matrix quadratic form. -/
theorem sphereQuadraticForm_add_matrix (A B : Matrix I I ℂ) (z : EuclideanSpace ℂ I) :
    sphereQuadraticForm (A+B) z=sphereQuadraticForm A z+sphereQuadraticForm B z := by
  simp [sphereQuadraticForm,mul_add,add_mul,Finset.sum_add_distrib]

/-- The exact normal-order decomposition of a centered quadratic square. -/
theorem complexGaussianNormalMatrix_square_identity (H : Matrix I I ℂ) (z : I → ℂ) :
    (sphereQuadraticForm H (WithLp.toLp 2 z)-Matrix.trace H)^2 =
      Matrix.trace (H^2)+2*(sphereQuadraticForm (H^2) (WithLp.toLp 2 z)-Matrix.trace (H^2))+
      complexGaussianNormalMatrix H H z := by
  rw [complexGaussianNormalMatrix,sphereQuadraticForm_add_matrix]
  simp only [pow_two]
  ring
omit [DecidableEq I] in
/-- Scaling the actual coordinate vector by a real scalar scales every quadratic form by its square. -/
theorem sphereQuadraticForm_real_scale (A : Matrix I I ℂ) (s : ℝ) (z : I → ℂ) :
    sphereQuadraticForm A (WithLp.toLp 2 (fun i => s • z i))=
      ((s^2:ℝ):ℂ)*sphereQuadraticForm A (WithLp.toLp 2 z) := by
  simp only [sphereQuadraticForm,Complex.real_smul,star_mul,Complex.star_def,Complex.conj_ofReal,
    Complex.ofReal_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Quadratic

section Operators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

/-- The actual centered readout score; qscale=1 is Gaussian and qscale=D is the unit-sphere score. -/
def readoutCenteredScore (H : Ω → Matrix I I ℂ) (h qscale : ℝ) (z : I → ℂ) (ω : Ω) : ℂ :=
  (qscale:ℂ)*sphereQuadraticForm (H ω) (WithLp.toLp 2 z)-(h:ℂ)

/-- Genuine full first-moment matrix for the readout reference measure. -/
def readoutMeanOperator (μ : Measure Ω) (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (h qscale : ℝ) (z : I → ℂ) : Matrix I I ℂ :=
  D • ∫ ω,readoutCenteredScore H h qscale z ω • P ω∂μ

/-- Genuine full second moment, not just its quadratic auxiliary part. -/
def readoutSecondOperator (μ : Measure Ω) (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (h qscale : ℝ) (z : I → ℂ) : Matrix I I ℂ :=
  D • ∫ ω,(readoutCenteredScore H h qscale z ω)^2 • P ω∂μ

/-- The same quadratic auxiliary operator, defined using H squared and its true trace scale nu. -/
def readoutAuxiliaryOperator (μ : Measure Ω) (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (nu qscale : ℝ) (z : I → ℂ) : Matrix I I ℂ :=
  D • ∫ ω,(2*((qscale:ℂ)*sphereQuadraticForm ((H ω)^2) (WithLp.toLp 2 z)-(nu:ℂ))) • P ω∂μ

variable [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [DecidableEq I] [BorelSpace Ω] [CompactSpace Ω] in
/-- The score's actual finite polynomial expression is continuous in the complete record. -/
theorem readoutCenteredScore_continuous (H : Ω → Matrix I I ℂ) (hH : Continuous H)
    (h qscale : ℝ) (z : I → ℂ) : Continuous (readoutCenteredScore H h qscale z) := by
  unfold readoutCenteredScore sphereQuadraticForm
  fun_prop

/-- The exact Gaussian full-second-moment identity, with all matrix integrals justified by compact-record continuity. -/
theorem readoutSecondOperator_gaussian_identity (D h nu : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H)
    (htr : ∀ ω,Matrix.trace (H ω)=(h:ℂ)) (htr2 : ∀ ω,Matrix.trace ((H ω)^2)=(nu:ℂ))
    (hnorm : D • (∫ ω,P ω∂μ)=1) (z : I → ℂ) :
    readoutSecondOperator μ D P H h 1 z = nu • (1:Matrix I I ℂ)+
      readoutAuxiliaryOperator μ D P H nu 1 z+normalReadoutRemainder μ D P H z := by
  have hi (f : Ω → Matrix I I ℂ) (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (ω : Ω) : (readoutCenteredScore H h 1 z ω)^2 • P ω =
      nu • P ω+(2*(sphereQuadraticForm ((H ω)^2) (WithLp.toLp 2 z)-(nu:ℂ))) • P ω+
      complexGaussianNormalMatrix (H ω) (H ω) z • P ω := by
    have he := complexGaussianNormalMatrix_square_identity (H ω) z
    rw [htr,htr2] at he
    simp only [readoutCenteredScore,Complex.ofReal_one,one_mul]
    rw [he,add_smul,add_smul]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  unfold readoutSecondOperator
  simp_rw [he]
  rw [integral_add (hi _ (by unfold sphereQuadraticForm; fun_prop))
      (normalReadoutRemainder_integrand_integrable μ P H hP hH z),
    integral_add (hi _ (by fun_prop)) (hi _ (by unfold sphereQuadraticForm; fun_prop)),integral_smul,
    smul_add,smul_add,smul_comm D nu,hnorm]
  simp only [readoutAuxiliaryOperator,normalReadoutRemainder,Complex.ofReal_one,one_mul]

/-- The exact pointwise scalar identity behind the full second moment on normalized targets. -/
theorem readoutCenteredScore_scaled_square (h nu qscale s : ℝ) (H : Matrix I I ℂ)
    (htr : Matrix.trace H=(h:ℂ)) (htr2 : Matrix.trace (H^2)=(nu:ℂ)) (z : I → ℂ) :
    ((qscale:ℂ)*sphereQuadraticForm H (WithLp.toLp 2 (fun i => s • z i))-(h:ℂ))^2 =
      (nu:ℂ)+(qscale*s^2:ℝ)*(2*((qscale:ℂ)*sphereQuadraticForm (H^2)
        (WithLp.toLp 2 (fun i => s • z i))-(nu:ℂ)))+
      ((qscale*s^2)^2:ℝ)*complexGaussianNormalMatrix H H z+
      (2*(qscale*s^2-1)*h:ℝ)*((qscale:ℂ)*sphereQuadraticForm H
        (WithLp.toLp 2 (fun i => s • z i))-(h:ℂ))-
      ((qscale*s^2-1)^2*(nu+h^2):ℝ) := by
  simp only [sphereQuadraticForm_real_scale,complexGaussianNormalMatrix,
    sphereQuadraticForm_add_matrix,← pow_two,htr,htr2,
    Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_pow,
    Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

/-- The complete radial second-moment identity is an equality of actual Bochner matrices. -/
theorem readoutSecondOperator_scaled_identity (D h nu qscale s : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H)
    (htr : ∀ ω,Matrix.trace (H ω)=(h:ℂ)) (htr2 : ∀ ω,Matrix.trace ((H ω)^2)=(nu:ℂ))
    (hnorm : D • (∫ ω,P ω∂μ)=1) (z : I → ℂ) :
    readoutSecondOperator μ D P H h qscale (fun i => s • z i) =
      nu • (1:Matrix I I ℂ)+(qscale*s^2) •
        readoutAuxiliaryOperator μ D P H nu qscale (fun i => s • z i)+
      (qscale*s^2)^2 • normalReadoutRemainder μ D P H z+
      (2*(qscale*s^2-1)*h) • readoutMeanOperator μ D P H h qscale (fun i => s • z i)-
      ((qscale*s^2-1)^2*(nu+h^2)) • (1:Matrix I I ℂ) := by
  have hi (f : Ω → Matrix I I ℂ) (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (ω : Ω) : (readoutCenteredScore H h qscale (fun i => s • z i) ω)^2 • P ω =
      nu • P ω+(qscale*s^2) • ((2*((qscale:ℂ)*sphereQuadraticForm ((H ω)^2)
        (WithLp.toLp 2 (fun i => s • z i))-(nu:ℂ))) • P ω)+
      (qscale*s^2)^2 • (complexGaussianNormalMatrix (H ω) (H ω) z • P ω)+
      (2*(qscale*s^2-1)*h) • (readoutCenteredScore H h qscale (fun i => s • z i) ω • P ω)-
      ((qscale*s^2-1)^2*(nu+h^2)) • P ω := by
    ext i j
    have hs := congrArg (fun v : ℂ => v * P ω i j)
      (readoutCenteredScore_scaled_square h nu qscale s (H ω) (htr ω) (htr2 ω) z)
    simpa only [readoutCenteredScore,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
      Complex.real_smul,smul_eq_mul,add_mul,sub_mul,mul_assoc] using hs
  let F : Ω → Matrix I I ℂ := fun ω => (2*((qscale:ℂ)*sphereQuadraticForm ((H ω)^2)
    (WithLp.toLp 2 (fun i => s • z i))-(nu:ℂ))) • P ω
  let G : Ω → Matrix I I ℂ := fun ω => complexGaussianNormalMatrix (H ω) (H ω) z • P ω
  let J : Ω → Matrix I I ℂ := fun ω => readoutCenteredScore H h qscale (fun i => s • z i) ω • P ω
  have hF : Continuous F := by dsimp [F]; unfold sphereQuadraticForm; fun_prop
  have hG : Continuous G := normalReadoutRemainder_integrand_continuous P H hP hH z
  have hJ : Continuous J := (readoutCenteredScore_continuous H hH h qscale _).smul hP
  have h0 := (hi P hP).smul nu
  have h1 := (hi F hF).smul (qscale*s^2)
  have h2 := (hi G hG).smul ((qscale*s^2)^2)
  have h3 := (hi J hJ).smul (2*(qscale*s^2-1)*h)
  have h4 := (hi P hP).smul ((qscale*s^2-1)^2*(nu+h^2))
  unfold readoutSecondOperator
  simp_rw [he]
  change D • (∫ ω,nu • P ω+(qscale*s^2) • F ω+(qscale*s^2)^2 • G ω+
    (2*(qscale*s^2-1)*h) • J ω-((qscale*s^2-1)^2*(nu+h^2)) • P ω∂μ)=_
  have hsub := integral_sub (((h0.add h1).add h2).add h3) h4
  have ha3 := integral_add ((h0.add h1).add h2) h3
  have ha2 := integral_add (h0.add h1) h2
  have ha1 := integral_add h0 h1
  simp only [Pi.add_apply,Pi.smul_apply] at hsub ha3 ha2 ha1
  rw [hsub,ha3,ha2,ha1]
  simp only [integral_smul,smul_add,smul_sub,smul_comm D,hnorm,readoutAuxiliaryOperator,
    readoutMeanOperator,normalReadoutRemainder,F,G,J]


/-- The inverse common radius t=norm(z)^2/D, using the actual Euclidean norm. -/
def readoutRadialAlpha (D : ℝ) (z : I → ℂ) : ℝ := D/‖(WithLp.toLp 2 z : EuclideanSpace ℂ I)‖^2

omit [MeasurableSpace Ω] [DecidableEq I] [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω] in
theorem readoutRadialAlpha_eq_inverse_radius (D : ℝ) (z : I → ℂ) :
    readoutRadialAlpha D z=(‖(WithLp.toLp 2 z : EuclideanSpace ℂ I)‖^2/D)⁻¹ := by
  simp [readoutRadialAlpha]

/-- Full second-moment identity at the normalized direction of a nonzero vector. -/
theorem readoutSecondOperator_direction_identity (D h nu : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H)
    (htr : ∀ ω,Matrix.trace (H ω)=(h:ℂ)) (htr2 : ∀ ω,Matrix.trace ((H ω)^2)=(nu:ℂ))
    (hnorm : D • (∫ ω,P ω∂μ)=1) (z : I → ℂ)
    (hz : (WithLp.toLp 2 z : EuclideanSpace ℂ I)≠0)
    (e₀ : Metric.sphere (0 : EuclideanSpace ℂ I) 1) :
    let ψ : I → ℂ := (sphereDirection e₀ (WithLp.toLp 2 z) : EuclideanSpace ℂ I)
    let a := readoutRadialAlpha D z
    readoutSecondOperator μ D P H h D ψ =
      nu • (1:Matrix I I ℂ)+a • readoutAuxiliaryOperator μ D P H nu D ψ+
      a^2 • normalReadoutRemainder μ D P H z+
      (2*(a-1)*h) • readoutMeanOperator μ D P H h D ψ-
      ((a-1)^2*(nu+h^2)) • (1:Matrix I I ℂ) := by
  have hd : (sphereDirection e₀ (WithLp.toLp 2 z) : EuclideanSpace ℂ I).ofLp=
      (fun i => ‖(WithLp.toLp 2 z : EuclideanSpace ℂ I)‖⁻¹ • z i) := by
    funext i
    rw [sphereDirection_coe]
    simp only [hz,ite_false]
    rfl
  have ha : D*(‖(WithLp.toLp 2 z : EuclideanSpace ℂ I)‖⁻¹)^2=readoutRadialAlpha D z := by
    rw [readoutRadialAlpha,inv_pow,div_eq_mul_inv]
  dsimp only
  rw [hd]
  simpa only [ha] using readoutSecondOperator_scaled_identity μ D h nu D
    ‖(WithLp.toLp 2 z : EuclideanSpace ℂ I)‖⁻¹ P H hP hH htr htr2 hnorm z

end Operators

end CertificationGaussian
