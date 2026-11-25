import LocalCertification.Quantum.Weyl
import Mathlib.LinearAlgebra.Matrix.Reindex

open scoped BigOperators
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

/-- Reindexing does not change the trace. -/
theorem matrix_reindex_trace {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Matrix α α ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

variable {d : ℕ} [NeZero d]

/-- Canonical cyclic coordinates, rather than an arbitrary finite enumeration. -/
def weylIndexEquiv (d : ℕ) [NeZero d] : Fin d ≃ ZMod d := (ZMod.finEquiv d).toEquiv

/-- The same X^a Z^b matrices on the computational Fin d basis; cyclic labels stay explicit. -/
def localWeylFin (u : ZMod d × ZMod d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (weylIndexEquiv d).symm (localWeyl u)

theorem localWeylFin_apply (u : ZMod d × ZMod d) (x y : Fin d) :
    localWeylFin u x y =
      if weylIndexEquiv d x = weylIndexEquiv d y + u.1
      then ZMod.stdAddChar (u.2 * weylIndexEquiv d y) else 0 := rfl

@[simp] theorem localWeylFin_zero : localWeylFin (0 : ZMod d × ZMod d) = 1 := by
  simp [localWeylFin]

theorem localWeylFin_adjoint_mul (u : ZMod d × ZMod d) :
    (localWeylFin u).conjTranspose * localWeylFin u = 1 := by
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (weylIndexEquiv d).symm)
    (localWeyl_adjoint_mul u)
  simpa only [localWeylFin, map_mul, map_one, Matrix.coe_reindexAlgEquiv,
    Matrix.conjTranspose_reindex] using h

theorem localWeylFin_mul_adjoint (u : ZMod d × ZMod d) :
    localWeylFin u * (localWeylFin u).conjTranspose = 1 := by
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ (weylIndexEquiv d).symm)
    (localWeyl_mul_adjoint u)
  simpa only [localWeylFin, map_mul, map_one, Matrix.coe_reindexAlgEquiv,
    Matrix.conjTranspose_reindex] using h

theorem localWeylFin_hilbertSchmidt (u v : ZMod d × ZMod d) :
    ((localWeylFin u).conjTranspose * localWeylFin v).trace =
      if u = v then (d : ℂ) else 0 := by
  have h := matrix_reindex_trace (weylIndexEquiv d).symm
    ((localWeyl u).conjTranspose * localWeyl v)
  rw [localWeyl_hilbertSchmidt] at h
  change (Matrix.reindexAlgEquiv ℂ ℂ (weylIndexEquiv d).symm
    ((localWeyl u).conjTranspose * localWeyl v)).trace = _ at h
  simpa only [localWeylFin, map_mul, Matrix.coe_reindexAlgEquiv,
    Matrix.conjTranspose_reindex] using h

theorem localWeylFin_contraction (x y z t : Fin d) :
    (∑ u : ZMod d × ZMod d, localWeylFin u x z * star (localWeylFin u y t)) =
      (d : ℂ) * (1 : Matrix (Fin d) (Fin d) ℂ) x y *
        (1 : Matrix (Fin d) (Fin d) ℂ) z t := by
  simpa only [localWeylFin, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Matrix.one_apply, (weylIndexEquiv d).injective.eq_iff] using
    localWeyl_contraction (weylIndexEquiv d x) (weylIndexEquiv d y)
      (weylIndexEquiv d z) (weylIndexEquiv d t)

theorem localWeylFin_adjoint_contraction (x y z t : Fin d) :
    (∑ u : ZMod d × ZMod d, star (localWeylFin u z x) * localWeylFin u t y) =
      (d : ℂ) * (1 : Matrix (Fin d) (Fin d) ℂ) x y *
        (1 : Matrix (Fin d) (Fin d) ℂ) z t := by
  have h := localWeylFin_contraction (d := d) t z y x
  by_cases hxy : x = y <;> by_cases hzt : z = t <;>
    simpa [mul_comm, Matrix.one_apply, hxy, hzt, eq_comm] using h

theorem localWeylFin_injective : Function.Injective (localWeylFin (d := d)) :=
  (Matrix.reindexAlgEquiv ℂ ℂ (weylIndexEquiv d).symm).injective.comp localWeyl_injective

@[simp] theorem localWeylFin_eq_one_iff (u : ZMod d × ZMod d) :
    localWeylFin u = 1 ↔ u = 0 := by
  rw [← localWeylFin_zero, localWeylFin_injective.eq_iff]

end LocalCertification.Quantum
