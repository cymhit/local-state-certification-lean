import LocalCertification.Quantum.WeylTensor
import CertificationGaussian.HammingKernel

open scoped BigOperators
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

variable {d : ℕ} [NeZero d] {n : ℕ}

/-- Support is defined by nonidentity local Weyl labels, equivalently by nonidentity matrices. -/
def weylSupport (u : WeylLabel d n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u i ≠ 0)

def weylWeight (u : WeylLabel d n) : ℕ := (weylSupport u).card

def weylShell (d n j : ℕ) [NeZero d] : Finset (WeylLabel d n) :=
  Finset.univ.filter (fun u => weylWeight u = j)

theorem weylSupport_matrix (u : WeylLabel d n) :
    weylSupport u = Finset.univ.filter (fun i => localWeylFin (u i) ≠ 1) := by
  simp [weylSupport]

/-- Counting transport uses its actual zero reference word, not a zero-preserving enumeration assumption. -/
def weylWordEquiv (d n : ℕ) [NeZero d] :
    WeylLabel d n ≃ CertificationGaussian.QuditIndex (Fintype.card (ZMod d × ZMod d)) n :=
  Equiv.piCongrRight (fun _ : Fin n => Fintype.equivFin (ZMod d × ZMod d))

theorem weylSupport_eq_differenceSupport (u : WeylLabel d n) :
    weylSupport u = CertificationGaussian.differenceSupport
      (weylWordEquiv d n 0) (weylWordEquiv d n u) := by
  ext i
  simp only [weylSupport, CertificationGaussian.differenceSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, weylWordEquiv, Equiv.piCongrRight_apply]
  exact not_congr (by simp [eq_comm])

theorem weylSupport_fiber_card (s : Finset (Fin n)) :
    Fintype.card {u : WeylLabel d n // weylSupport u = s} = (d^2 - 1)^s.card := by
  let e := (weylWordEquiv d n).subtypeEquiv
    (p := fun u => weylSupport u = s)
    (q := fun y => CertificationGaussian.differenceSupport (weylWordEquiv d n 0) y = s)
    (fun u => by rw [weylSupport_eq_differenceSupport])
  rw [Fintype.card_congr e, CertificationGaussian.card_differenceFiber]
  simp [sq]

/-- Exact shell size, valid also for empty powers and out-of-range shells. -/
theorem weylShell_card (j : ℕ) :
    (weylShell d n j).card = Nat.choose n j * (d^2 - 1)^j := by
  let e := (weylWordEquiv d n).subtypeEquiv
    (p := fun u => weylWeight u = j)
    (q := fun y => CertificationGaussian.hammingDistance (weylWordEquiv d n 0) y = j)
    (fun u => by rw [weylWeight, weylSupport_eq_differenceSupport,
      CertificationGaussian.card_differenceSupport])
  rw [weylShell, ← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_subtype,
    CertificationGaussian.hamming_sphere_card]
  simp [sq]

theorem weylShell_card_pos (hd : 2 ≤ d) {j : ℕ} (hj : j ≤ n) :
    0 < (weylShell d n j).card := by
  rw [weylShell_card]
  apply Nat.mul_pos (Nat.choose_pos hj)
  apply Nat.pow_pos
  have : 1 < d^2 := by nlinarith
  omega

omit [NeZero d] in
@[simp] theorem weylWeight_eq_zero (u : WeylLabel d n) :
    weylWeight u = 0 ↔ u = 0 := by
  simp only [weylWeight, Finset.card_eq_zero, weylSupport, Finset.filter_eq_empty_iff]
  simp [funext_iff]

@[simp] theorem weylShell_zero : weylShell d n 0 = {0} := by
  ext u
  simp [weylShell]

end LocalCertification.Quantum
