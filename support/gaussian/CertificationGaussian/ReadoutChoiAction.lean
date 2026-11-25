import CertificationGaussian.ReadoutChoiTensor
import CertificationGaussian.UnitarySphereConjugation

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- The genuine Choi contraction in the fixed Bell input/output order. -/
def choiVectorAction {I : Type*} [Fintype I] (J : Matrix (I×I) (I×I) ℂ)
    (z : I → ℂ) : Matrix I I ℂ :=
  fun a b => (Fintype.card I:ℂ)*∑ i,∑ j,J (i,a) (j,b)*z i*star (z j)

/-- The actual weighted Bell matrix acts as the original dimension-scaled Gaussian conjugation. -/
theorem choiVectorAction_weightedBell {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (W : K → Matrix I I ℂ) (c : K → ℝ) (z : I → ℂ) :
    choiVectorAction (weightedBellMatrix W c) z=
      (Fintype.card I:ℂ) • unitaryWeightedRankOne W c z := by
  rw [← matrixSesquilinear_unitaryChaosCoefficient,← chaosFlattening₃_unitaryChaosCoefficient]
  ext a b
  simp only [choiVectorAction,chaosFlattening₃,matrixSesquilinear,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Contracting the weighted Bell matrix against a vector gives its weighted conjugation operator. -/
theorem choiVectorAction_weightedBell_clm {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (W : K → Matrix I I ℂ) (c : K → ℝ) (ψ : EuclideanSpace ℂ I) :
    rectangularEuclideanCLM (choiVectorAction (weightedBellMatrix W c) ψ.ofLp)=
      unitarySphereConjugation W c ψ := by
  rw [choiVectorAction_weightedBell]
  rfl

section ActualIntegral
variable {Ω I : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [DecidableEq I] in
/-- The actual quadratic integrand contracts the transposed input entry, with all finite sums integrable. -/
theorem readout_quadratic_integral_entry (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) (z : I → ℂ) (a b : I) :
    (∫ ω,sphereQuadraticForm (H ω) (WithLp.toLp 2 z)*P ω a b∂μ)=
      ∑ i,∑ j,(∫ ω,P ω a b*H ω j i∂μ)*z i*star (z j) := by
  have hi (f : Ω → ℂ) (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (ω : Ω) : sphereQuadraticForm (H ω) (WithLp.toLp 2 z)*P ω a b=
      ∑ i,∑ j,(P ω a b*H ω j i)*z i*star (z j) := by
    unfold sphereQuadraticForm
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi _ (by fun_prop))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi _ (by fun_prop))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const,integral_mul_const]

/-- A Choi matrix built from the actual readout integral acts as card(I)*D times that same quadratic matrix integral. -/
theorem choiVectorAction_readout (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) (z : I → ℂ) :
    choiVectorAction (readoutChoiMatrix μ D P H) z=
      ((Fintype.card I:ℝ)*D) • (∫ ω,sphereQuadraticForm (H ω) (WithLp.toLp 2 z) • P ω∂μ) := by
  ext a b
  rw [Matrix.smul_apply,matrix_entry_integral μ _ (by unfold sphereQuadraticForm; fun_prop)]
  simp only [Matrix.smul_apply,smul_eq_mul]
  rw [readout_quadratic_integral_entry μ P H hP hH z a b]
  simp only [choiVectorAction,readoutChoiMatrix,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_natCast,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The true centered first readout moment is the Choi action minus its original scalar center. -/
theorem readoutMeanOperator_choi (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) (h : ℝ)
    (hnorm : (Fintype.card I:ℝ) • (∫ ω,P ω∂μ)=1) (z : I → ℂ) :
    readoutMeanOperator μ (Fintype.card I:ℝ) P H h (Fintype.card I:ℝ) z=
      choiVectorAction (readoutChoiMatrix μ (Fintype.card I:ℝ) P H) z-h • (1:Matrix I I ℂ) := by
  have hi (f : Ω → Matrix I I ℂ) (hf : Continuous f) : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [choiVectorAction_readout μ _ P H hP hH z]
  unfold readoutMeanOperator readoutCenteredScore
  simp_rw [sub_smul,mul_smul]
  rw [integral_sub (hi _ (by unfold sphereQuadraticForm; fun_prop)) (hi _ (by fun_prop)),
    integral_smul,integral_smul,smul_sub]
  have hs (c : ℝ) (A : Matrix I I ℂ) : (c:ℂ) • A=c • A := by
    ext i j
    change (c:ℂ)*A i j=c • A i j
    exact Complex.real_smul.symm
  rw [hs,hs,smul_comm (Fintype.card I:ℝ) h,hnorm,smul_smul]
end ActualIntegral

end CertificationGaussian
