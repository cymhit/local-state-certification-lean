import LocalCertification.Quantum.WeylFin
import LocalCertification.Quantum.TensorMatrix
import CertificationGaussian.Model

open scoped BigOperators
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

/-- Independent canonical shift/phase labels at each site. -/
abbrev WeylLabel (d n : ℕ) := Fin n → ZMod d × ZMod d

/-- The actual tensor product of canonical Weyl matrices on the sole qudit index. -/
def quditWeyl {d : ℕ} [NeZero d] {n : ℕ} (u : WeylLabel d n) :
    Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ :=
  tensorMatrix (fun i => localWeylFin (u i))

theorem quditWeyl_apply {d : ℕ} [NeZero d] {n : ℕ} (u : WeylLabel d n)
    (x y : CertificationGaussian.QuditIndex d n) :
    quditWeyl u x y = ∏ i, localWeylFin (u i) (x i) (y i) := rfl

variable {d : ℕ} [NeZero d] {n : ℕ}

@[simp] theorem quditWeyl_zero : quditWeyl (0 : WeylLabel d n) = 1 := by
  simp [quditWeyl, tensorMatrix_one]

theorem quditWeyl_adjoint_mul (u : WeylLabel d n) :
    (quditWeyl u).conjTranspose * quditWeyl u = 1 := by
  rw [quditWeyl, ← tensorMatrix_adjoint]
  rw [← tensorMatrix_mul (fun i : Fin n => (localWeylFin (u i)).conjTranspose)
    (fun i : Fin n => localWeylFin (u i))]
  simp_rw [localWeylFin_adjoint_mul]
  exact tensorMatrix_one

theorem quditWeyl_mul_adjoint (u : WeylLabel d n) :
    quditWeyl u * (quditWeyl u).conjTranspose = 1 := by
  rw [quditWeyl, ← tensorMatrix_adjoint]
  rw [← tensorMatrix_mul (fun i : Fin n => localWeylFin (u i))
    (fun i : Fin n => (localWeylFin (u i)).conjTranspose)]
  simp_rw [localWeylFin_mul_adjoint]
  exact tensorMatrix_one

/-- Orthogonality has the physical dimension d^n, including n=0. -/
theorem quditWeyl_hilbertSchmidt (u v : WeylLabel d n) :
    ((quditWeyl u).conjTranspose * quditWeyl v).trace =
      if u = v then (d : ℂ)^n else 0 := by
  simp only [quditWeyl, ← tensorMatrix_adjoint]
  rw [← tensorMatrix_mul (fun i : Fin n => (localWeylFin (u i)).conjTranspose)
    (fun i : Fin n => localWeylFin (v i)), tensorMatrix_trace]
  simp_rw [localWeylFin_hilbertSchmidt]
  rw [Fintype.prod_ite_zero]
  simp [← funext_iff]

theorem quditWeyl_contraction (x y z t : CertificationGaussian.QuditIndex d n) :
    (∑ u : WeylLabel d n, quditWeyl u x z * star (quditWeyl u y t)) =
      (d : ℂ)^n * (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) x y *
        (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) z t := by
  simp only [quditWeyl_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (κ := fun _ : Fin n => ZMod d × ZMod d)
    (fun i a => localWeylFin a (x i) (z i) * star (localWeylFin a (y i) (t i)))]
  simp_rw [localWeylFin_contraction]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h (a b : CertificationGaussian.QuditIndex d n) :
      (∏ i, (1 : Matrix (Fin d) (Fin d) ℂ) (a i) (b i)) =
        (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) a b :=
    congrArg (fun M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ => M a b)
      (tensorMatrix_one (ι := Fin n) (α := Fin d))
  rw [h, h]

theorem quditWeyl_adjoint_contraction (x y z t : CertificationGaussian.QuditIndex d n) :
    (∑ u : WeylLabel d n, star (quditWeyl u z x) * quditWeyl u t y) =
      (d : ℂ)^n * (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) x y *
        (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) z t := by
  have h := quditWeyl_contraction (d := d) t z y x
  by_cases hxy : x = y <;> by_cases hzt : z = t <;>
    simpa [mul_comm, Matrix.one_apply, hxy, hzt, eq_comm] using h

/-- Complete twirl for every global matrix, not just tensor-product inputs. -/
theorem quditWeyl_twirl
    (A : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) :
    (∑ u : WeylLabel d n, quditWeyl u * A * (quditWeyl u).conjTranspose) =
      ((d : ℂ)^n * A.trace) • (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) := by
  exact sum_sandwich_of_entry_contraction quditWeyl (fun u => (quditWeyl u).conjTranspose)
    ((d : ℂ)^n) quditWeyl_contraction A

theorem quditWeyl_adjoint_twirl
    (A : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) :
    (∑ u : WeylLabel d n, (quditWeyl u).conjTranspose * A * quditWeyl u) =
      ((d : ℂ)^n * A.trace) • (1 : Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ) := by
  exact sum_sandwich_of_entry_contraction (fun u => (quditWeyl u).conjTranspose) quditWeyl
    ((d : ℂ)^n) quditWeyl_adjoint_contraction A

theorem quditWeyl_injective : Function.Injective (quditWeyl (d := d) (n := n)) := by
  intro u v huv
  by_contra hne
  have h := quditWeyl_hilbertSchmidt u v
  have hself := quditWeyl_hilbertSchmidt u u
  rw [← huv, hself] at h
  simp only [ite_true, hne, ite_false] at h
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (NeZero.ne d)) h

@[simp] theorem quditWeyl_eq_one_iff (u : WeylLabel d n) :
    quditWeyl u = 1 ↔ u = 0 := by
  rw [← quditWeyl_zero, quditWeyl_injective.eq_iff]

end LocalCertification.Quantum
