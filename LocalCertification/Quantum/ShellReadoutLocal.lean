import LocalCertification.Quantum.ProductMeasurement

open scoped BigOperators ComplexOrder
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

variable {d : ℕ} [NeZero d]

theorem localWeylFin_adjoint_twirl_actual (B : Matrix (Fin d) (Fin d) ℂ) :
    (∑ u : ZMod d × ZMod d, (localWeylFin u).conjTranspose * B * localWeylFin u) =
      ((d : ℂ) * B.trace) • (1 : Matrix (Fin d) (Fin d) ℂ) :=
  sum_sandwich_of_entry_contraction (fun u => (localWeylFin u).conjTranspose) localWeylFin
    (d : ℂ) localWeylFin_adjoint_contraction B

theorem localWeylFin_nonzero_readout (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.trace = 1) :
    (∑ u ∈ Finset.univ.erase (0 : ZMod d × ZMod d),
      (localWeylFin u).conjTranspose * B * localWeylFin u) =
      (d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - B := by
  have h := Finset.sum_erase_add (Finset.univ (α := ZMod d × ZMod d))
    (fun u => (localWeylFin u).conjTranspose * B * localWeylFin u) (Finset.mem_univ 0)
  rw [localWeylFin_adjoint_twirl_actual, hB, mul_one] at h
  simpa using eq_sub_of_add_eq h

/-- Every continuous local unitary basis has the same exact one-site shell readout. -/
theorem local_basis_shell_readout (U : CertificationGaussian.LocalUnitary d) (x : Fin d) :
    (∑ u ∈ Finset.univ.erase (0 : ZMod d × ZMod d),
      (localWeylFin u).conjTranspose * (basisPOVM U).effects x * localWeylFin u) =
      ((d : ℂ) - 1) • (basisPOVM U).effects x +
        (d : ℂ) • ∑ y ∈ Finset.univ.erase x, (basisPOVM U).effects y := by
  rw [localWeylFin_nonzero_readout _ (basisPOVM_effect_trace U x)]
  have h := Finset.sum_erase_add (Finset.univ (α := Fin d))
    (fun y => (basisPOVM U).effects y) (Finset.mem_univ x)
  rw [(basisPOVM U).sum_eq_one] at h
  rw [eq_sub_of_add_eq h]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

variable {n : ℕ}

/-- Entrywise tensor multiplication uses the actual local Weyl matrices. -/
theorem quditWeyl_adjoint_tensor (u : WeylLabel d n)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (quditWeyl u).conjTranspose * tensorMatrix B * quditWeyl u =
      tensorMatrix (fun i => (localWeylFin (u i)).conjTranspose * B i * localWeylFin (u i)) := by
  simp only [quditWeyl, ← tensorMatrix_adjoint]
  rw [← tensorMatrix_mul (fun i => (localWeylFin (u i)).conjTranspose) B]
  rw [← tensorMatrix_mul (fun i => (localWeylFin (u i)).conjTranspose * B i)
    (fun i => localWeylFin (u i))]

/-- The allowed local labels express an exact support, including the identity off the support. -/
def supportLocalLabels (s : Finset (Fin n)) (i : Fin n) : Finset (ZMod d × ZMod d) :=
  if i ∈ s then Finset.univ.erase 0 else {0}

theorem weylSupport_eq_iff_local (u : WeylLabel d n) (s : Finset (Fin n)) :
    weylSupport u = s ↔ ∀ i, u i ∈ supportLocalLabels s i := by
  simp only [Finset.ext_iff, weylSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ s <;> simp [supportLocalLabels, hi]

/-- Finite product expansion with an independently restricted label at each site. -/
theorem sum_product_restricted {β : Type*} [Fintype β] [DecidableEq β]
    (t : Fin n → Finset β) (f : Fin n → β → ℂ) :
    (∑ u : Fin n → β, if ∀ i, u i ∈ t i then ∏ i, f i (u i) else 0) =
      ∏ i, ∑ a ∈ t i, f i a := by
  calc
    _ = ∑ u : Fin n → β, ∏ i, if u i ∈ t i then f i (u i) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Fintype.prod_ite_zero]
      by_cases h : ∀ i, u i ∈ t i <;> simp [h]
    _ = ∏ i, ∑ a : β, if a ∈ t i then f i a else 0 :=
      (Fintype.prod_sum (fun i a => if a ∈ t i then f i a else 0)).symm
    _ = _ := by simp

/-- Exact support Weyl conjugation factors as a product of the proved local shell maps. -/
theorem fixedSupport_adjoint_tensor (s : Finset (Fin n))
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (∑ u ∈ Finset.univ.filter (fun u : WeylLabel d n => weylSupport u = s),
      (quditWeyl u).conjTranspose * tensorMatrix B * quditWeyl u) =
      tensorMatrix (fun i => ∑ a ∈ supportLocalLabels s i,
        (localWeylFin a).conjTranspose * B i * localWeylFin a) := by
  simp_rw [quditWeyl_adjoint_tensor]
  rw [Finset.sum_filter]
  ext x y
  simp only [Matrix.sum_apply, tensorMatrix, Matrix.ite_apply, Matrix.zero_apply]
  simp_rw [weylSupport_eq_iff_local]
  exact sum_product_restricted (supportLocalLabels s)
    (fun (i : Fin n) (a : ZMod d × ZMod d) =>
      ((localWeylFin a).conjTranspose * B i * localWeylFin a) (x i) (y i))

/-- Fixed-support action on the genuine product-basis projectors. -/
theorem fixedSupport_projector (s : Finset (Fin n))
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    (∑ u ∈ Finset.univ.filter (fun u : WeylLabel d n => weylSupport u = s),
      (quditWeyl u).conjTranspose * (productBasisPOVM d n U).effects x * quditWeyl u) =
      tensorMatrix (fun i => if i ∈ s then
        ((d : ℂ) - 1) • (basisPOVM (U i)).effects (x i) +
          (d : ℂ) • ∑ y ∈ Finset.univ.erase (x i), (basisPOVM (U i)).effects y
        else (basisPOVM (U i)).effects (x i)) := by
  rw [productBasisPOVM_effect, fixedSupport_adjoint_tensor]
  congr 1
  funext i
  by_cases hi : i ∈ s
  · simp only [supportLocalLabels, hi, ite_true]
    exact local_basis_shell_readout (U i) (x i)
  · simp [supportLocalLabels, hi]

end LocalCertification.Quantum
