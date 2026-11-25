import LocalCertification.Quantum.ShellReadoutLocal

open scoped BigOperators ComplexOrder
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum

variable {d n : ℕ}

/-- The actual one-site readout coefficients before shell normalization. -/
def supportTransition (s : Finset (Fin n)) (i : Fin n) (x y : Fin d) : ℂ :=
  if i ∈ s then (if y = x then (d : ℂ) - 1 else d) else (if y = x then 1 else 0)

theorem supportTransition_basis_sum (s : Finset (Fin n)) (i : Fin n)
    (U : CertificationGaussian.LocalUnitary d) (x : Fin d) :
    (∑ y, supportTransition s i x y • (basisPOVM U).effects y) =
      if i ∈ s then ((d : ℂ) - 1) • (basisPOVM U).effects x +
        (d : ℂ) • ∑ y ∈ Finset.univ.erase x, (basisPOVM U).effects y
      else (basisPOVM U).effects x := by
  have he : Finset.univ.filter (fun y : Fin d => y = x) = {x} := by ext y; simp
  by_cases hi : i ∈ s
  · simp only [supportTransition, hi, ite_true, ite_smul]
    rw [Finset.sum_ite]
    simp [he, ← Finset.smul_sum, Finset.filter_ne']
  · simp [supportTransition, hi, ite_smul]

/-- Tensor product distributes over all independently indexed local effect sums. -/
theorem tensorMatrix_sum (A : Fin n → Fin d → Matrix (Fin d) (Fin d) ℂ) :
    tensorMatrix (fun i => ∑ y, A i y) =
      ∑ y : CertificationGaussian.QuditIndex d n, tensorMatrix (fun i => A i (y i)) := by
  ext x z
  simp only [tensorMatrix, Matrix.sum_apply]
  exact Fintype.prod_sum (fun i y => A i y (x i) (z i))

/-- Fixed-support readout expressed directly in the actual product measurement outcomes. -/
theorem fixedSupport_projector_outcomes [NeZero d] (s : Finset (Fin n))
    (U : Fin n → CertificationGaussian.LocalUnitary d) (x : CertificationGaussian.QuditIndex d n) :
    (∑ u ∈ Finset.univ.filter (fun u : WeylLabel d n => weylSupport u = s),
      (quditWeyl u).conjTranspose * (productBasisPOVM d n U).effects x * quditWeyl u) =
      ∑ y : CertificationGaussian.QuditIndex d n,
        (∏ i, supportTransition s i (x i) (y i)) • (productBasisPOVM d n U).effects y := by
  rw [fixedSupport_projector]
  simp_rw [← supportTransition_basis_sum s _ (U _) (x _)]
  rw [tensorMatrix_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [productBasisPOVM_effect]
  ext a b
  simp only [tensorMatrix, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- The fixed-support coefficient depends only on the actual mismatch set. -/
theorem supportTransition_prod (s : Finset (Fin n)) (x y : CertificationGaussian.QuditIndex d n) :
    (∏ i, supportTransition s i (x i) (y i)) =
      if CertificationGaussian.differenceSupport x y ⊆ s then
        ((d : ℂ) - 1)^(s.card - CertificationGaussian.hammingDistance x y) *
          (d : ℂ)^(CertificationGaussian.hammingDistance x y) else 0 := by
  let t := CertificationGaussian.differenceSupport x y
  by_cases hsub : t ⊆ s
  · rw [ite_eq_left hsub]
    have hout (i : Fin n) (hi : i ∉ s) : y i = x i := by
      by_contra hne
      have ht : i ∈ t := by simp [t, CertificationGaussian.differenceSupport, Ne.symm hne]
      exact hi (hsub ht)
    have hp : (∏ i, supportTransition s i (x i) (y i)) =
        ∏ i ∈ s, if y i = x i then (d : ℂ)-1 else d := by
      calc
        _ = ∏ i ∈ s, supportTransition s i (x i) (y i) := by
          symm
          apply Finset.prod_subset (Finset.subset_univ s)
          intro i hi his
          simp [supportTransition, his, hout i his]
        _ = _ := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [supportTransition, hi]
    rw [hp, Finset.prod_ite]
    have he : s.filter (fun i => y i = x i) = s \ t := by
      ext i
      simp [t, CertificationGaussian.differenceSupport, eq_comm]
    have hn : s.filter (fun i => ¬ y i = x i) = t := by
      ext i
      have ht : i ∈ t ↔ y i ≠ x i := by simp [t, CertificationGaussian.differenceSupport, eq_comm]
      simp only [Finset.mem_filter, ← ht]
      exact and_iff_right_of_imp (fun hi => hsub hi)
    rw [he, hn]
    simp only [Finset.prod_const, Finset.card_sdiff_of_subset hsub]
    rfl
  · rw [ite_eq_right hsub]
    obtain ⟨i, hit, his⟩ := Finset.not_subset.mp hsub
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hne : y i ≠ x i := by simpa [t, CertificationGaussian.differenceSupport, eq_comm] using hit
    simp [supportTransition, his, hne]

/-- Summing all supports of a fixed size counts exactly the supersets of the mismatch set. -/
theorem supportTransition_shell_sum (j : ℕ) (x y : CertificationGaussian.QuditIndex d n) :
    (∑ s ∈ Finset.univ.powersetCard j, ∏ i, supportTransition s i (x i) (y i)) =
      if CertificationGaussian.hammingDistance x y ≤ j then
        (Nat.choose (n - CertificationGaussian.hammingDistance x y) (j - CertificationGaussian.hammingDistance x y) : ℂ) *
          (((d : ℂ)-1)^(j - CertificationGaussian.hammingDistance x y) *
            (d : ℂ)^(CertificationGaussian.hammingDistance x y)) else 0 := by
  let t := CertificationGaussian.differenceSupport x y
  have ht : t.card = CertificationGaussian.hammingDistance x y := rfl
  have he : (∑ s ∈ Finset.univ.powersetCard j, ∏ i, supportTransition s i (x i) (y i)) =
      ∑ s ∈ Finset.univ.powersetCard j, if t ⊆ s then
        ((d : ℂ)-1)^(j - t.card) * (d : ℂ)^t.card else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    rw [supportTransition_prod, hc, ← ht]
  rw [he, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hk : t.card ≤ j
  · rw [ite_eq_left (ht ▸ hk)]
    rw [Finset.card_filter_powersetCard_subset t Finset.univ j (Finset.subset_univ t) hk]
    simp only [Finset.card_univ, Fintype.card_fin, ht]
  · rw [ite_eq_right (ht ▸ hk)]
    have hempty : ((Finset.univ (α := Fin n)).powersetCard j).filter (t ⊆ ·) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hp := Finset.mem_filter.mp hs
      have hc := (Finset.mem_powersetCard.mp hp.1).2
      exact hk (hc ▸ Finset.card_le_card hp.2)
    rw [hempty]
    simp

end LocalCertification.Quantum
