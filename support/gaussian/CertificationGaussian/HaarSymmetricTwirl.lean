module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import QIT.Symmetry.UnitaryTwirl
import QIT.Util.CMatrixCLM

/-! # The Haar second tensor as the normalized symmetric projection -/

@[expose] public section
noncomputable section
open MeasureTheory QIT
open scoped Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

private theorem compactHaar_integral_borel (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (m m' : MeasurableSpace G)
    (b : @BorelSpace G _ m) (b' : @BorelSpace G _ m') (f : G → ℂ) :
    (letI := m; letI := b; ∫ x, f x ∂Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) =
    (letI := m'; letI := b'; ∫ x, f x ∂Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) := by
  have he : m = m' := b.measurable_eq.trans b'.measurable_eq.symm
  cases he
  rfl

omit [Fintype I] [Nonempty I] in
private theorem symmetric_projection_entry (a b c d : I) :
    symmetricProjectionMatrix (a := I) 2 (twoCopyTensorWord a b) (twoCopyTensorWord c d) =
      ((if a=c then 1 else 0)*(if b=d then 1 else 0) +
       (if b=c then 1 else 0)*(if a=d then 1 else 0)) / 2 := by
  rw [symmetricProjectionMatrix_two_eq_half_one_add_swap]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
    twoCopyTensorWord_eq_iff]
  simp [tensorPowerSwapMatrix_two, permutationMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix, permEquiv_twoCopySwapPerm_twoCopyTensorWord, twoCopyTensorWord_eq_iff,
    ite_and, mul_ite, div_eq_inv_mul]
  split_ifs <;> rfl

/-- The Haar tensor of a single column on two copies is the normalized
symmetric projection. Its antisymmetric weight is zero and its trace is one. -/
theorem haar_column_tensor_eq_normalized_symmetric_projection [Nontrivial I] (j : I) :
    unitaryTwirl 2 (Matrix.single (twoCopyTensorWord j j) (twoCopyTensorWord j j) (1 : ℂ)) =
      (1 / ((Fintype.card I : ℂ)*((Fintype.card I : ℂ)+1)/2)) •
        symmetricProjectionMatrix (a := I) 2 := by
  let w := twoCopyTensorWord j j
  have tr (M : CMatrix (TensorPower I 2)) : (M * Matrix.single w w (1:ℂ)).trace = M w w := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single, ite_and]
  have hs : (symmetricProjectionMatrix (a := I) 2 * Matrix.single w w (1:ℂ)).trace = 1 := by
    rw [tr, symmetric_projection_entry]
    norm_num
  have ha : (antisymmetricProjectionMatrix_two (a := I) * Matrix.single w w (1:ℂ)).trace = 0 := by
    rw [antisymmetricProjectionMatrix_two, Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, hs]
    simp [Matrix.trace, Matrix.diag, Matrix.single]
  rw [unitaryTwirl_two_eq_symmetric_antisymmetric_trace_decomposition,
    hs, ha, symmetricProjectionMatrix_two_trace, zero_div, zero_smul, add_zero]

omit [Nonempty I] in
private theorem column_twirl_integrand (j a b c d : I) (U : Matrix.unitaryGroup I ℂ) :
    unitaryTwirlIntegrand 2
      (Matrix.single (twoCopyTensorWord j j) (twoCopyTensorWord j j) (1:ℂ)) U
      (twoCopyTensorWord b d) (twoCopyTensorWord a c) =
        star (U.val a j)*U.val b j*star (U.val c j)*U.val d j := by
  simp [unitaryTwirlIntegrand, Matrix.mul_apply, Matrix.single, ite_and, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, unitaryTensorPowerMatrix_apply_eq_fin_prod, Fin.prod_univ_two]
  ring

/-- Coordinate form of the trace-normalized symmetric tensor for a Haar
column. This follows by evaluating the averaged operator at two tensor words. -/
private theorem column_fourth_symmetric [Nontrivial I] (j a b c d : I) :
    (∫ U : Matrix.unitaryGroup I ℂ,
      star (U.val a j)*U.val b j*star (U.val c j)*U.val d j ∂unitaryHaarMeasure) =
      ((if a=b then 1 else 0)*(if c=d then 1 else 0) +
       (if a=d then 1 else 0)*(if c=b then 1 else 0)) /
        ((Fintype.card I : ℂ)*((Fintype.card I : ℂ)+1)) := by
  let A := Matrix.single (twoCopyTensorWord j j) (twoCopyTensorWord j j) (1:ℂ)
  let x := twoCopyTensorWord b d
  let y := twoCopyTensorWord a c
  have h := congrArg (fun T : CMatrix (TensorPower I 2) => T x y)
    (haar_column_tensor_eq_normalized_symmetric_projection j)
  change unitaryTwirl 2 A x y = _ at h
  have he : unitaryTwirl 2 A x y =
      ∫ U : Matrix.unitaryGroup I ℂ, unitaryTwirlIntegrand 2 A U x y ∂unitaryHaarMeasure := by
    simpa [unitaryTwirl, cMatrixEntryCLM] using
      ((cMatrixEntryCLM x y).integral_comp_comm (unitaryTwirl_integrand_integrable 2 A)).symm
  have hcard : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsucc : (Fintype.card I : ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (Fintype.card I : ℝ)+1 ≠ 0 by positivity)
  calc
    _ = ∫ U : Matrix.unitaryGroup I ℂ, unitaryTwirlIntegrand 2 A U x y ∂unitaryHaarMeasure := by
      exact integral_congr_ae (.of_forall (fun U => (column_twirl_integrand j a b c d U).symm))
    _ = unitaryTwirl 2 A x y := he.symm
    _ = _ := by
      rw [h]
      simp only [x, y, Matrix.smul_apply, smul_eq_mul, symmetric_projection_entry]
      simp only [show b = a ↔ a = b from eq_comm, show d = c ↔ c = d from eq_comm,
          show d = a ↔ a = d from eq_comm, show b = c ↔ c = b from eq_comm]
      field_simp

/-- The symmetric tensor identity for the normalized Haar measure, expressed
using any Borel presentation of the same unitary group. -/
theorem haar_column_fourth_moment_symmetric [Nontrivial I] [CompactSpace (Matrix.unitaryGroup I ℂ)]
    [IsTopologicalGroup (Matrix.unitaryGroup I ℂ)] (m : MeasurableSpace (Matrix.unitaryGroup I ℂ))
    (bm : @BorelSpace (Matrix.unitaryGroup I ℂ) _ m) (j a b c d : I) :
    (letI := m; letI := bm; ∫ U : Matrix.unitaryGroup I ℂ,
      star (U.val a j)*U.val b j*star (U.val c j)*U.val d j ∂Measure.haarMeasure ⊤) =
      ((if a=b then 1 else 0)*(if c=d then 1 else 0) +
       (if a=d then 1 else 0)*(if c=b then 1 else 0)) /
        ((Fintype.card I : ℂ)*((Fintype.card I : ℂ)+1)) :=
  (compactHaar_integral_borel _ m _ bm _ _).trans (column_fourth_symmetric j a b c d)

end CertificationGaussian
