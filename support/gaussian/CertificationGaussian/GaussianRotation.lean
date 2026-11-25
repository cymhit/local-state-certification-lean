import CertificationGaussian.GaussianBlocks
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open MeasureTheory ProbabilityTheory
namespace CertificationGaussian
variable (I : Type*) [Fintype I]

/-- The genuine real orthonormal basis of complex Euclidean coordinate space. -/
def complexRealBasis : OrthonormalBasis (Fin 2 × I) ℝ (EuclideanSpace ℂ I) :=
  (Pi.orthonormalBasis (fun _ : I => Complex.orthonormalBasisOneI)).reindex
    ((Equiv.sigmaEquivProd I (Fin 2)).trans (Equiv.prodComm I (Fin 2)))

def complexRealIsometry : EuclideanSpace ℝ (Fin 2 × I) ≃ₗᵢ[ℝ] EuclideanSpace ℂ I :=
  (complexRealBasis I).repr.symm

theorem complexRealIsometry_toLp (x : (Fin 2 × I) → ℝ) :
    complexRealIsometry I (WithLp.toLp 2 x) =
      WithLp.toLp 2 (fun i => (x (0,i) : ℂ) + (x (1,i) : ℂ) * Complex.I) := by
  apply (complexRealBasis I).repr.injective
  change (complexRealBasis I).repr ((complexRealBasis I).repr.symm _) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext ⟨s,i⟩
  fin_cases s <;>
    simp [complexRealBasis, OrthonormalBasis.repr_reindex, Pi.orthonormalBasis_repr,
      Complex.orthonormalBasisOneI_repr_apply]

def complexGaussianLift (x : (Fin 2 × I) → ℝ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (complexCoordinate x)

theorem complexGaussianLift_eq (x : (Fin 2 × I) → ℝ) :
    complexGaussianLift I x = (Real.sqrt 2)⁻¹ • complexRealIsometry I (WithLp.toLp 2 x) := by
  rw [complexRealIsometry_toLp]
  ext i
  simp only [complexGaussianLift, complexCoordinate, PiLp.smul_apply, PiLp.toLp_apply,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, div_eq_mul_inv]
  ring

omit [Fintype I] in
@[fun_prop] theorem complexGaussianLift_continuous : Continuous (complexGaussianLift I) := by
  unfold complexGaussianLift complexCoordinate
  fun_prop

theorem complexRealIsometry_gaussian_map :
    (pairedGaussian I).map (fun x => complexRealIsometry I (WithLp.toLp 2 x)) =
      stdGaussian (EuclideanSpace ℂ I) := by
  rw [← Function.comp_def, ← Measure.map_map (complexRealIsometry I).continuous.measurable
    (by fun_prop)]
  rw [pairedGaussian, map_pi_eq_stdGaussian, stdGaussian_map]

theorem complexGaussianLift_map :
    (pairedGaussian I).map (complexGaussianLift I) =
      (stdGaussian (EuclideanSpace ℂ I)).map (fun z => (Real.sqrt 2)⁻¹ • z) := by
  have he : complexGaussianLift I = (fun z : EuclideanSpace ℂ I => (Real.sqrt 2)⁻¹ • z) ∘
      (fun x => complexRealIsometry I (WithLp.toLp 2 x)) := by
    funext x; exact complexGaussianLift_eq I x
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), complexRealIsometry_gaussian_map]

variable {I} [DecidableEq I]
/-- A complex unitary matrix also acts as an actual real linear isometry. -/
def matrixUnitaryRealIsometry (A : Matrix I I ℂ) (hA : A ∈ unitary (Matrix I I ℂ)) :
    EuclideanSpace ℂ I ≃ₗᵢ[ℝ] EuclideanSpace ℂ I :=
  let T : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ I :=
    Unitary.linearIsometryEquiv ⟨Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A,
      Unitary.map_mem (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) hA⟩
  { T.toLinearEquiv.restrictScalars ℝ with norm_map' := T.norm_map }

theorem matrixUnitaryRealIsometry_apply (A : Matrix I I ℂ)
    (hA : A ∈ unitary (Matrix I I ℂ)) (z : I → ℂ) :
    matrixUnitaryRealIsometry A hA (WithLp.toLp 2 z) = WithLp.toLp 2 (A.mulVec z) := rfl

/-- Isotropy is preserved by the actual 1/sqrt(2) scalar normalization. -/
theorem complexGaussianLift_unitary_map (A : Matrix I I ℂ)
    (hA : A ∈ unitary (Matrix I I ℂ)) :
    ((pairedGaussian I).map (complexGaussianLift I)).map (matrixUnitaryRealIsometry A hA) =
      (pairedGaussian I).map (complexGaussianLift I) := by
  let T := matrixUnitaryRealIsometry A hA
  rw [complexGaussianLift_map]
  change ((stdGaussian (EuclideanSpace ℂ I)).map (fun z => (Real.sqrt 2)⁻¹ • z)).map T = _
  rw [Measure.map_map T.continuous.measurable (by fun_prop)]
  have he : T ∘ (fun z : EuclideanSpace ℂ I => (Real.sqrt 2)⁻¹ • z) =
      (fun z : EuclideanSpace ℂ I => (Real.sqrt 2)⁻¹ • z) ∘ T := by
    funext z
    exact T.map_smul _ _
  rw [he, ← Measure.map_map (by fun_prop) T.continuous.measurable, stdGaussian_map]

/-- The actual coordinate-valued complex Gaussian law is invariant under every unitary matrix. -/
theorem complexCoordinate_unitary_map (A : Matrix I I ℂ)
    (hA : A ∈ unitary (Matrix I I ℂ)) :
    (pairedGaussian I).map (fun x => A.mulVec (complexCoordinate x)) =
      (pairedGaussian I).map complexCoordinate := by
  let T := matrixUnitaryRealIsometry A hA
  have hmT : Measurable T := T.continuous.measurable
  have hmL := (complexGaussianLift_continuous I).measurable
  have hmO : Measurable (WithLp.ofLp : EuclideanSpace ℂ I → I → ℂ) := by fun_prop
  have h := congrArg (fun ν : Measure (EuclideanSpace ℂ I) => ν.map WithLp.ofLp)
    (complexGaussianLift_unitary_map A hA)
  change (((pairedGaussian I).map (complexGaussianLift I)).map T).map WithLp.ofLp = _ at h
  rw [Measure.map_map hmO hmT, Measure.map_map (hmO.comp hmT) hmL,
    Measure.map_map hmO hmL] at h
  exact h

/-- In particular this applies to the conjugate transpose in the existing quartic model. -/
theorem complexCoordinate_conjTranspose_map (U : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) :
    (pairedGaussian I).map (fun x => U.conjTranspose.mulVec (complexCoordinate x)) =
      (pairedGaussian I).map complexCoordinate :=
  complexCoordinate_unitary_map U.conjTranspose (Unitary.star_mem hU)

end CertificationGaussian
