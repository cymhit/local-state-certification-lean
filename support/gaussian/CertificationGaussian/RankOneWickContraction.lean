import CertificationGaussian.ComplexGaussianMatrixWick
import CertificationGaussian.HaarOverlapSixth

noncomputable section
open Matrix
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I]

/-- The genuine rank-one matrix v w† on the original Euclidean coordinates. -/
def vectorRankOne (v w : EuclideanSpace ℂ I) : Matrix I I ℂ :=
  fun i j => v i*star (w j)

/-- Matrix multiplication contracts the middle actual vector coordinates. -/
theorem vectorRankOne_mul (v w u z : EuclideanSpace ℂ I) :
    vectorRankOne v w*vectorRankOne u z = (inner ℂ w u) • vectorRankOne v z := by
  ext i j
  simp only [Matrix.mul_apply,vectorRankOne,Matrix.smul_apply,smul_eq_mul,
    PiLp.inner_apply,RCLike.inner_apply',Complex.star_def,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem vectorRankOne_trace (v w : EuclideanSpace ℂ I) :
    Matrix.trace (vectorRankOne v w)=inner ℂ w v := by
  simp only [Matrix.trace,Matrix.diag,vectorRankOne,PiLp.inner_apply,RCLike.inner_apply',Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The output trace contributes precisely the four-cycle, for actual matrices. -/
theorem vectorRankOne_four_trace (v₀ v₁ v₂ v₃ : EuclideanSpace ℂ I) :
    Matrix.trace (vectorRankOne v₀ v₀*vectorRankOne v₁ v₁*
      vectorRankOne v₂ v₂*vectorRankOne v₃ v₃) =
      inner ℂ v₀ v₁*inner ℂ v₁ v₂*inner ℂ v₂ v₃*inner ℂ v₃ v₀ := by
  rw [vectorRankOne_mul,Matrix.smul_mul,vectorRankOne_mul,smul_smul,
    Matrix.smul_mul,vectorRankOne_mul,smul_smul,Matrix.trace_smul,vectorRankOne_trace]
  rfl

/-- Exact tensor-permutation contraction, with the existing genuine permutation-matrix convention. -/
theorem vectorRankOne_wick_trace [DecidableEq I] {T : Type*} [Fintype T] [DecidableEq T]
    (v : T → EuclideanSpace ℂ I) (π : Equiv.Perm T) :
    Matrix.trace (wickTensorMatrix (fun t => vectorRankOne (v t) (v t))*
      wickTensorPermutationMatrix π) = ∏ t,inner ℂ (v (π t)) (v t) := by
  rw [wickTensorMatrix_permutation_trace]
  have he (x : T → I) : (∏ t,vectorRankOne (v t) (v t) (x t) (x (π.symm t))) =
      ∏ t,star (v (π t) (x t))*v t (x t) := by
    simp only [vectorRankOne,Finset.prod_mul_distrib]
    have hp : (∏ t,star (v t (x (π.symm t)))) = (∏ t,star (v (π t) (x t))) := by
      symm
      simpa only [Equiv.symm_apply_apply] using
        Equiv.prod_comp π (fun t => star (v t (x (π.symm t))))
    rw [hp,mul_comm]
  simp_rw [he]
  calc
    _ = ∏ t,∑ i,star (v (π t) i)*v t i :=
      (Fintype.prod_sum (fun t i => star (v (π t) i)*v t i)).symm
    _ = _ := by simp only [PiLp.inner_apply,RCLike.inner_apply',Complex.star_def]

/-- Norms remove orientations only after the true complex matrix contraction is proved. -/
theorem vectorRankOne_wick_trace_norm [DecidableEq I] {T : Type*} [Fintype T] [DecidableEq T]
    (v : T → EuclideanSpace ℂ I) (π : Equiv.Perm T) :
    ‖Matrix.trace (wickTensorMatrix (fun t => vectorRankOne (v t) (v t))*
      wickTensorPermutationMatrix π)‖ = ∏ t,‖inner ℂ (v t) (v (π t))‖ := by
  rw [vectorRankOne_wick_trace,norm_prod]
  apply Finset.prod_congr rfl
  intro t _
  exact norm_inner_symm _ _

/-- This rank-one matrix equals the full-record Haar projector. -/
theorem vectorRankOne_haarRecord (d : ℕ) [NeZero d]
    (ω : ComplexUnitary (Fin d) × Fin d) :
    vectorRankOne (haarRecordedUnitVector d ω).val (haarRecordedUnitVector d ω).val =
      recordedProjector d ω := by
  ext i j
  exact (haarRecordedUnitVector_projector d ω i j).symm

end CertificationGaussian
