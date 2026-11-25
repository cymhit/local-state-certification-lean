import LocalCertification.Quantum.MeasurablePOVMMap
import LocalCertification.Quantum.FixedBlockIndex

/-! Hilbert-coordinate transport of the original matrix POVM. Outcome spaces,
labels, and measurable events remain literal; no rank-one refinement is used. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder
noncomputable section
namespace LocalCertification.Quantum

private def matrixReindexHom {I J : Type*} (e : I ≃ J) :
    Matrix I I ℂ →+ Matrix J J ℂ where
  toFun A := A.submatrix e.symm e.symm
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem matrixReindexHom_continuous {I J : Type*} (e : I ≃ J) :
    Continuous (matrixReindexHom e) := by
  change Continuous (fun A : Matrix I I ℂ => A.submatrix e.symm e.symm)
  fun_prop

namespace MeasurablePOVM
variable {Ω I J : Type*} [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def reindexHilbert (M : MeasurablePOVM Ω I) (e : I ≃ J) : MeasurablePOVM Ω J where
  toVectorMeasure := M.toVectorMeasure.mapRange (matrixReindexHom e) (matrixReindexHom_continuous e)
  positive A hA := by
    change ((M.toVectorMeasure A).submatrix e.symm e.symm).PosSemidef
    exact (M.positive A hA).submatrix e.symm
  univ := by
    change (M.toVectorMeasure Set.univ).submatrix e.symm e.symm = 1
    rw [M.univ, Matrix.submatrix_one_equiv]

theorem reindexHilbert_apply (M : MeasurablePOVM Ω I) (e : I ≃ J) (A : Set Ω) :
    (M.reindexHilbert e).toVectorMeasure A =
      (M.toVectorMeasure A).submatrix e.symm e.symm := rfl

theorem born_reindexHilbert (M : MeasurablePOVM Ω I) (e : I ≃ J) (ρ : QIT.State I) :
    (M.reindexHilbert e).born (ρ.reindex e) = M.born ρ := by
  ext A hA
  rw [born_apply _ _ hA, born_apply _ _ hA, reindexHilbert_apply, QIT.State.reindex_matrix,
    trace_mul_reindex]

theorem born_reindexHilbert_input (M : MeasurablePOVM Ω I) (e : I ≃ J) (ρ : QIT.State J) :
    (M.reindexHilbert e).born ρ = M.born (ρ.reindex e.symm) := by
  have h := born_reindexHilbert M e (ρ.reindex e.symm)
  have he : (ρ.reindex e.symm).reindex e = ρ := (stateReindexEquiv e).right_inv ρ
  rw [he] at h
  exact h

theorem traceReference_reindexHilbert (M : MeasurablePOVM Ω I) (e : I ≃ J) :
    (M.reindexHilbert e).traceReference = M.traceReference := by
  ext A hA
  rw [traceReference_apply _ hA, traceReference_apply _ hA, reindexHilbert_apply,
    ← Fintype.card_congr e]
  have ht : ((M.toVectorMeasure A).submatrix e.symm e.symm).trace =
      (M.toVectorMeasure A).trace := Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  rw [ht]

theorem reindexHilbert_inverse (M : MeasurablePOVM Ω I) (e : I ≃ J) :
    (M.reindexHilbert e).reindexHilbert e.symm = M := by
  apply ext_vectorMeasure
  apply VectorMeasure.ext
  intro A _
  rw [reindexHilbert_apply, reindexHilbert_apply]
  ext i j
  simp only [Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

def reindexHilbertEquiv (e : I ≃ J) : MeasurablePOVM Ω I ≃ MeasurablePOVM Ω J where
  toFun M := M.reindexHilbert e
  invFun M := M.reindexHilbert e.symm
  left_inv M := reindexHilbert_inverse M e
  right_inv M := reindexHilbert_inverse M e.symm

end MeasurablePOVM
namespace POVMKernel
variable {H Ω I J : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def reindexHilbert (K : POVMKernel H Ω I) (e : I ≃ J) : POVMKernel H Ω J where
  measurement h := (K.measurement h).reindexHilbert e
  measurable_effect A hA := by
    change Measurable (fun h => ((K.measurement h).toVectorMeasure A).submatrix e.symm e.symm)
    exact (matrixReindexHom_continuous e).measurable.comp (K.measurable_effect A hA)

theorem reindexHilbert_measurement (K : POVMKernel H Ω I) (e : I ≃ J) (h : H) :
    (K.reindexHilbert e).measurement h = (K.measurement h).reindexHilbert e := rfl

theorem bornKernel_reindexHilbert (K : POVMKernel H Ω I) (e : I ≃ J) (ρ : QIT.State I) :
    (K.reindexHilbert e).bornKernel (ρ.reindex e) = K.bornKernel ρ := by
  ext1 h
  exact MeasurablePOVM.born_reindexHilbert (K.measurement h) e ρ

theorem bornKernel_reindexHilbert_input (K : POVMKernel H Ω I) (e : I ≃ J) (ρ : QIT.State J) :
    (K.reindexHilbert e).bornKernel ρ = K.bornKernel (ρ.reindex e.symm) := by
  ext1 h
  exact MeasurablePOVM.born_reindexHilbert_input (K.measurement h) e ρ

theorem traceKernel_reindexHilbert (K : POVMKernel H Ω I) (e : I ≃ J) :
    (K.reindexHilbert e).traceKernel = K.traceKernel := by
  ext1 h
  exact MeasurablePOVM.traceReference_reindexHilbert (K.measurement h) e

theorem reindexHilbert_inverse (K : POVMKernel H Ω I) (e : I ≃ J) :
    (K.reindexHilbert e).reindexHilbert e.symm = K := by
  apply ext_measurement
  intro h
  exact MeasurablePOVM.reindexHilbert_inverse (K.measurement h) e

theorem exists_hilbert_reindex (e : I ≃ J) (K : POVMKernel H Ω I) :
    ∃ L : POVMKernel H Ω J,
      (∀ h A, (L.measurement h).toVectorMeasure A =
        ((K.measurement h).toVectorMeasure A).submatrix e.symm e.symm) ∧
      (∀ ρ : QIT.State I, L.bornKernel (ρ.reindex e) = K.bornKernel ρ) ∧
      (∀ h, (L.measurement h).traceReference = (K.measurement h).traceReference) :=
  ⟨K.reindexHilbert e, fun h A => MeasurablePOVM.reindexHilbert_apply (K.measurement h) e A,
    bornKernel_reindexHilbert K e, fun h => MeasurablePOVM.traceReference_reindexHilbert (K.measurement h) e⟩

end POVMKernel
end LocalCertification.Quantum
