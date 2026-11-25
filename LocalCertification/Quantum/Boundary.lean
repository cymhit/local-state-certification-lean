/- Algebraic qudit boundary interfaces using the common CertificationGaussian.QuditIndex. -/
import CertificationGaussian.Model
import QIT.Core.System
import QIT.States.Geometry.PureTargetFidelity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fin.Tuple.Basic

/-! Algebraic boundary interfaces for qudit states.
The only matrix norm scope is the Euclidean L² induced operator norm.
No restriction d ≥ 2 is needed for these interfaces. -/

open scoped Matrix.Norms.L2Operator
open Matrix WithLp

set_option autoImplicit false

noncomputable section
namespace LocalCertification.Quantum

universe u v w x

/-- Recursive tensor labels are function labels, including the empty power. -/
def tensorPowerEquiv (α : Type u) : (n : ℕ) → QIT.TensorPower α n ≃ (Fin n → α)
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => PUnit.unit
        left_inv := by intro a; cases a; rfl
        right_inv := by intro a; funext i; exact Fin.elim0 i }
  | n + 1 =>
      { toFun := fun a => Fin.cons a.1 (tensorPowerEquiv α n a.2)
        invFun := fun a => (a 0, (tensorPowerEquiv α n).symm (Fin.tail a))
        left_inv := by
          intro a
          cases a
          simp
          rfl
        right_inv := by
          intro a
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail] }

theorem tensorPowerEquiv_zero (α : Type u) :
    tensorPowerEquiv α 0 PUnit.unit = (fun i : Fin 0 => Fin.elim0 i) := by
  rfl

theorem tensorPower_card (α : Type u) [Fintype α] (n : ℕ) :
    Fintype.card (QIT.TensorPower α n) = Fintype.card α ^ n := by
  calc
    Fintype.card (QIT.TensorPower α n) = Fintype.card (Fin n → α) :=
      Fintype.card_congr (tensorPowerEquiv α n)
    _ = Fintype.card α ^ n := by simp

def quditTensorEquiv (d n : ℕ) : QIT.TensorPower (Fin d) n ≃ CertificationGaussian.QuditIndex d n :=
  tensorPowerEquiv (Fin d) n

theorem qudit_card (d n : ℕ) : Fintype.card (CertificationGaussian.QuditIndex d n) = d ^ n := by
  simp [CertificationGaussian.QuditIndex]

theorem qudit_zero_card (d : ℕ) : Fintype.card (CertificationGaussian.QuditIndex d 0) = 1 := by
  simp

theorem rankOne_trace_norm_sq {ι : Type u} [Fintype ι] (v : ι → ℂ) :
    (QIT.rankOneMatrix v).trace = (‖(toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 : ℂ) := by
  rw [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq]
  simp [QIT.rankOneMatrix_trace, dotProduct, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem pure_amp_norm {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ψ : QIT.PureVector ι) : ‖(toLp 2 ψ.amp : EuclideanSpace ℂ ι)‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have h := ψ.trace_rankOne_eq_one
  rw [rankOne_trace_norm_sq, ← Complex.ofReal_pow, ← Complex.ofReal_one] at h
  simpa using Complex.ofReal_injective h

def pureTargetFidelity {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ψ : QIT.PureVector ι) (ρ : QIT.State ι) : ℝ :=
  (ψ.state.matrix * ρ.matrix).trace.re

theorem pureTargetFidelity_eq_squaredFidelity {ι : Type u} [Fintype ι] [DecidableEq ι]
    (ψ : QIT.PureVector ι) (ρ : QIT.State ι) :
    pureTargetFidelity ψ ρ = ρ.squaredFidelity ψ.state := by
  rw [QIT.State.squaredFidelity_pure_right_eq_trace]
  exact congrArg Complex.re (Matrix.trace_mul_comm ψ.state.matrix ρ.matrix)

/-- Explicitly rectangular Euclidean continuous linear map. -/
def matrixCLM {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

theorem matrixCLM_norm {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℂ) : ‖matrixCLM A‖ = ‖A‖ := by
  rfl

theorem matrix_reindex_l2_opNorm {ι : Type u} {κ : Type v} {ι' : Type w} {κ' : Type x}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    [DecidableEq κ] [DecidableEq κ']
    (er : ι ≃ ι') (ec : κ ≃ κ') (A : Matrix ι κ ℂ) :
    ‖Matrix.reindex er ec A‖ = ‖A‖ := by
  let erL := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ er
  let ecL := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ec
  have h : matrixCLM (Matrix.reindex er ec A) =
      (erL : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι').comp
        ((matrixCLM A).comp (ecL.symm : EuclideanSpace ℂ κ' →L[ℂ] EuclideanSpace ℂ κ)) := by
    ext a i
    dsimp only [erL, ecL]
    rw [LinearIsometryEquiv.piLpCongrLeft_symm]
    simpa [matrixCLM, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      LinearIsometryEquiv.piLpCongrLeft, Matrix.reindex_apply, Matrix.mulVec, dotProduct]
      using (Fintype.sum_equiv ec.symm
        (fun j : κ' => A (er.symm i) (ec.symm j) * a j)
        (fun j : κ => A (er.symm i) j * a (ec j)) (fun j => by simp))
  rw [← matrixCLM_norm, h]
  simp only [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, matrixCLM_norm]

theorem qubit_three_card : Fintype.card (CertificationGaussian.QuditIndex 2 3) = 8 := by
  simp [CertificationGaussian.QuditIndex]

theorem qutrit_two_card : Fintype.card (CertificationGaussian.QuditIndex 3 2) = 9 := by
  simp [CertificationGaussian.QuditIndex]


end LocalCertification.Quantum
