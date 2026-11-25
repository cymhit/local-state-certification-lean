import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped BigOperators
open Matrix
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

variable {d : ℕ} [NeZero d]

/-- The canonical character has unit modulus, for every nonzero modulus. -/
theorem weyl_character_star (x : ZMod d) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, Complex.star_def,
    ← Circle.coe_inv_eq_conj]
  exact congrArg ((↑) : Circle → ℂ)
    (AddChar.map_neg_eq_inv (ZMod.toCircle (N := d)) x).symm

theorem weyl_character_star_mul (x : ZMod d) :
    star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
  rw [weyl_character_star, ← AddChar.map_add_eq_mul]
  simp

theorem weyl_character_sum (t : ZMod d) :
    (∑ b : ZMod d, ZMod.stdAddChar (b * t)) = if t = 0 then (d : ℂ) else 0 := by
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    (AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar d))

/-- The paper's order is X^a Z^b: the phase is evaluated at the input column. -/
def localWeyl (u : ZMod d × ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  fun x y => if x = y + u.1 then ZMod.stdAddChar (u.2 * y) else 0

@[simp] theorem localWeyl_zero : localWeyl (0 : ZMod d × ZMod d) = 1 := by
  ext x y
  simp [localWeyl, Matrix.one_apply]

theorem localWeyl_mul_apply (u : ZMod d × ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (x y : ZMod d) :
    (localWeyl u * A) x y = ZMod.stdAddChar (u.2 * (x - u.1)) * A (x - u.1) y := by
  classical
  simp only [Matrix.mul_apply, localWeyl]
  have h (z : ZMod d) : x = z + u.1 ↔ z = x - u.1 := by
    constructor
    · intro hz; rw [hz]; simp
    · intro hz; rw [hz]; simp
  simp_rw [h]
  simp

theorem mul_localWeyl_apply (u : ZMod d × ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (x y : ZMod d) :
    (A * localWeyl u) x y = A x (y + u.1) * ZMod.stdAddChar (u.2 * y) := by
  classical
  simp [Matrix.mul_apply, localWeyl, mul_ite]

theorem localWeyl_adjoint_mul_apply (u : ZMod d × ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (x y : ZMod d) :
    ((localWeyl u).conjTranspose * A) x y =
      star (ZMod.stdAddChar (u.2 * x)) * A (x + u.1) y := by
  classical
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, localWeyl, apply_ite, ite_mul]

theorem mul_localWeyl_adjoint_apply (u : ZMod d × ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (x y : ZMod d) :
    (A * (localWeyl u).conjTranspose) x y =
      A x (y - u.1) * star (ZMod.stdAddChar (u.2 * (y - u.1))) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, localWeyl, apply_ite]
  have h (z : ZMod d) : y = z + u.1 ↔ z = y - u.1 := by
    constructor
    · intro hz; rw [hz]; simp
    · intro hz; rw [hz]; simp
  simp_rw [h]
  simp

theorem localWeyl_conjugate_apply (u : ZMod d × ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (x y : ZMod d) :
    (localWeyl u * A * (localWeyl u).conjTranspose) x y =
      ZMod.stdAddChar (u.2 * (x - y)) * A (x - u.1) (y - u.1) := by
  rw [mul_localWeyl_adjoint_apply, localWeyl_mul_apply, weyl_character_star]
  rw [mul_right_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem localWeyl_adjoint_conjugate_apply (u : ZMod d × ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (x y : ZMod d) :
    ((localWeyl u).conjTranspose * A * localWeyl u) x y =
      ZMod.stdAddChar (u.2 * (y - x)) * A (x + u.1) (y + u.1) := by
  rw [mul_localWeyl_apply, localWeyl_adjoint_mul_apply, weyl_character_star]
  rw [mul_right_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem localWeyl_adjoint_mul (u : ZMod d × ZMod d) :
    (localWeyl u).conjTranspose * localWeyl u = 1 := by
  ext x y
  rw [localWeyl_adjoint_mul_apply]
  by_cases h : x = y
  · subst y
    simp only [localWeyl, Matrix.one_apply_eq]
    exact weyl_character_star_mul _
  · simp [localWeyl, h]

theorem localWeyl_mul_adjoint (u : ZMod d × ZMod d) :
    localWeyl u * (localWeyl u).conjTranspose = 1 := by
  ext x y
  rw [mul_localWeyl_adjoint_apply]
  by_cases h : x = y
  · subst y
    simp only [localWeyl, sub_add_cancel, Matrix.one_apply_eq]
    rw [mul_comm]
    exact weyl_character_star_mul _
  · simp [localWeyl, h]

/-- Hilbert--Schmidt orthogonality, with no primality hypothesis. -/
theorem localWeyl_hilbertSchmidt (u v : ZMod d × ZMod d) :
    ((localWeyl u).conjTranspose * localWeyl v).trace =
      if u = v then (d : ℂ) else 0 := by
  classical
  simp only [Matrix.trace, Matrix.diag, localWeyl_adjoint_mul_apply, localWeyl]
  by_cases ha : u.1 = v.1
  · simp only [ha, ite_true]
    simp_rw [weyl_character_star, ← AddChar.map_add_eq_mul]
    have he (x : ZMod d) : -(u.2 * x) + v.2 * x = x * (v.2 - u.2) := by ring
    simp_rw [he]
    rw [weyl_character_sum]
    congr 1
    simp [Prod.ext_iff, ha, sub_eq_zero, eq_comm]
  · have h (x : ZMod d) : x + u.1 ≠ x + v.1 := by simpa using ha
    simp only [h, ite_false, mul_zero, Finset.sum_const_zero]
    have huv : u ≠ v := fun hh => ha (congrArg Prod.fst hh)
    simp [huv]

theorem localWeyl_injective : Function.Injective (localWeyl (d := d)) := by
  intro u v huv
  by_contra hne
  have h := localWeyl_hilbertSchmidt u v
  rw [← huv, localWeyl_adjoint_mul] at h
  simp [hne] at h
  exact NeZero.ne d h

@[simp] theorem localWeyl_eq_one_iff (u : ZMod d × ZMod d) :
    localWeyl u = 1 ↔ u = 0 := by
  rw [← localWeyl_zero, localWeyl_injective.eq_iff]

/-- The unnormalized complete Weyl twirl is dimension times the trace. -/
theorem localWeyl_twirl (A : Matrix (ZMod d) (ZMod d) ℂ) :
    (∑ u : ZMod d × ZMod d, localWeyl u * A * (localWeyl u).conjTranspose) =
      ((d : ℂ) * A.trace) • (1 : Matrix (ZMod d) (ZMod d) ℂ) := by
  classical
  ext x y
  simp only [Matrix.sum_apply, localWeyl_conjugate_apply, Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, weyl_character_sum]
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, ite_true, ← Finset.mul_sum]
    have ht : (∑ a : ZMod d, A (x - a) (x - a)) = A.trace := by
      exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)
    rw [ht]
    simp
  · simp [sub_ne_zero.mpr hxy, hxy, Matrix.smul_apply]

/-- The reverse conjugation has the same twirl, without assuming Weyl matrices Hermitian. -/
theorem localWeyl_adjoint_twirl (A : Matrix (ZMod d) (ZMod d) ℂ) :
    (∑ u : ZMod d × ZMod d, (localWeyl u).conjTranspose * A * localWeyl u) =
      ((d : ℂ) * A.trace) • (1 : Matrix (ZMod d) (ZMod d) ℂ) := by
  classical
  ext x y
  simp only [Matrix.sum_apply, localWeyl_adjoint_conjugate_apply, Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, weyl_character_sum]
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, ite_true, ← Finset.mul_sum]
    have ht : (∑ a : ZMod d, A (x + a) (x + a)) = A.trace := by
      exact Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
    rw [ht]
    simp
  · simp [sub_ne_zero.mpr (Ne.symm hxy), hxy, Matrix.smul_apply]

/-- The four-index contraction of the complete matrix basis. -/
theorem localWeyl_contraction (x y z t : ZMod d) :
    (∑ u : ZMod d × ZMod d, localWeyl u x z * star (localWeyl u y t)) =
      (d : ℂ) * (1 : Matrix (ZMod d) (ZMod d) ℂ) x y *
        (1 : Matrix (ZMod d) (ZMod d) ℂ) z t := by
  classical
  have hs (M : Matrix (ZMod d) (ZMod d) ℂ) :
      (M * Matrix.single z t (1 : ℂ) * M.conjTranspose) x y = M x z * star (M y t) := by
    simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]
  have h := congrArg (fun M : Matrix (ZMod d) (ZMod d) ℂ => M x y)
    (localWeyl_twirl (Matrix.single z t (1 : ℂ)))
  simp only [Matrix.sum_apply, hs] at h
  by_cases hzt : z = t
  · subst t
    simpa using h
  · simpa [Matrix.trace_single_eq_of_ne _ _ _ hzt, Matrix.one_apply, hzt] using h

/-- Removing the identity gives the exact one-site shell readout. -/
theorem localWeyl_nonzero_adjoint_twirl (B : Matrix (ZMod d) (ZMod d) ℂ)
    (hB : B.trace = 1) :
    (∑ u ∈ Finset.univ.erase (0 : ZMod d × ZMod d),
      (localWeyl u).conjTranspose * B * localWeyl u) =
      (d : ℂ) • (1 : Matrix (ZMod d) (ZMod d) ℂ) - B := by
  classical
  have h := Finset.sum_erase_add (Finset.univ (α := ZMod d × ZMod d))
    (fun u => (localWeyl u).conjTranspose * B * localWeyl u) (Finset.mem_univ 0)
  rw [localWeyl_adjoint_twirl, hB, mul_one] at h
  simpa using eq_sub_of_add_eq h

end LocalCertification.Quantum
