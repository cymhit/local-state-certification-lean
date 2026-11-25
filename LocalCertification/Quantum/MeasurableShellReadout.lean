import LocalCertification.Quantum.ShellReadoutNormalization

/-! Literal Weyl shell readout of arbitrary local trace-one matrices.
No orthogonal outcome basis is chosen. -/

open scoped BigOperators ComplexOrder
open Matrix Classical
set_option autoImplicit false
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ}

/-- Replace precisely the sites in `A` by their complementary effects. -/
def complementTensor (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (A : Finset (Fin n)) :
    Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ :=
  tensorMatrix (fun i => if i ∈ A then 1 - P i else P i)

/-- Cardinality average of normalized local complement factors. -/
def complementRadius (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    Matrix (CertificationGaussian.QuditIndex d n) (CertificationGaussian.QuditIndex d n) ℂ :=
  ((n.choose k : ℝ) * ((d-1 : ℕ) : ℝ)^k)⁻¹ •
    ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, complementTensor P A

theorem complementRadius_zero (P : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    complementRadius P 0 = tensorMatrix P := by
  simp [complementRadius, complementTensor]

/-- Multilinearity over all physical complement subsets. -/
theorem tensorMatrix_complement_expand (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin n → ℂ) :
    tensorMatrix (fun i => a i • P i + b i • (1 - P i)) =
      ∑ A : Finset (Fin n), (∏ i, if i ∈ A then b i else a i) • complementTensor P A := by
  ext x y
  simp only [tensorMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sum_apply, complementTensor]
  conv_lhs => arg 2; intro i; rw [add_comm]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro A _
  simp only [Matrix.ite_apply]
  rw [Finset.prod_ite, Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_notMem_eq_sdiff,
    ← Finset.compl_eq_univ_sdiff, Finset.prod_mul_distrib]
  ring

private def supportComplementCoefficient (s A : Finset (Fin n)) : ℂ :=
  ∏ i, if i ∈ A then (if i ∈ s then (d : ℂ) else 0)
    else (if i ∈ s then (d : ℂ)-1 else 1)

private theorem supportComplementCoefficient_eq (s A : Finset (Fin n)) :
    supportComplementCoefficient (d := d) s A =
      if A ⊆ s then ((d : ℂ)-1)^(s.card-A.card) * (d : ℂ)^A.card else 0 := by
  by_cases hsub : A ⊆ s
  · rw [ite_eq_left hsub]
    have hp : supportComplementCoefficient (d := d) s A =
        ∏ i ∈ s, if i ∈ A then (d : ℂ) else (d : ℂ)-1 := by
      unfold supportComplementCoefficient
      calc
        _ = ∏ i ∈ s, if i ∈ A then (if i ∈ s then (d : ℂ) else 0)
            else (if i ∈ s then (d : ℂ)-1 else 1) := by
          symm
          apply Finset.prod_subset (Finset.subset_univ s)
          intro i _ his
          have hia : i ∉ A := fun h => his (hsub h)
          simp [his, hia]
        _ = _ := Finset.prod_congr rfl (fun i hi => by simp [hi])
    rw [hp, Finset.prod_ite]
    have he : s.filter (fun i => i ∈ A) = A := by
      ext i
      simp only [Finset.mem_filter]
      exact and_iff_right_of_imp (fun hi => hsub hi)
    rw [he]
    simp only [Finset.filter_notMem_eq_sdiff, Finset.prod_const,
      Finset.card_sdiff_of_subset hsub]
    ring
  · rw [ite_eq_right hsub]
    obtain ⟨i, hiA, his⟩ := Finset.not_subset.mp hsub
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hiA, his])

private theorem supportComplementCoefficient_shell (j : ℕ) (A : Finset (Fin n)) :
    (∑ s ∈ Finset.univ.powersetCard j, supportComplementCoefficient (d := d) s A) =
      (shellReadoutCoefficient d n j A.card : ℂ) := by
  have he : (∑ s ∈ Finset.univ.powersetCard j, supportComplementCoefficient (d := d) s A) =
      ∑ s ∈ Finset.univ.powersetCard j,
        if A ⊆ s then ((d : ℂ)-1)^(j-A.card)*(d : ℂ)^A.card else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [supportComplementCoefficient_eq, (Finset.mem_powersetCard.mp hs).2]
  rw [he, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hk : A.card ≤ j
  · rw [Finset.card_filter_powersetCard_subset A Finset.univ j (Finset.subset_univ A) hk]
    simp [shellReadoutCoefficient, hk]
  · have hempty : ((Finset.univ : Finset (Fin n)).powersetCard j).filter (A ⊆ ·) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hp := Finset.mem_filter.mp hs
      have hc := (Finset.mem_powersetCard.mp hp.1).2
      exact hk (hc ▸ Finset.card_le_card hp.2)
    simp [hempty, shellReadoutCoefficient, hk]

theorem fixedSupport_complement_expand [NeZero d] (s : Finset (Fin n))
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (ht : ∀ i, (P i).trace = 1) :
    (∑ u ∈ Finset.univ.filter (fun u : WeylLabel d n => weylSupport u = s),
      (quditWeyl u).conjTranspose * tensorMatrix P * quditWeyl u) =
      ∑ A : Finset (Fin n),
        (if A ⊆ s then ((d : ℂ)-1)^(s.card-A.card)*(d : ℂ)^A.card else 0) •
          complementTensor P A := by
  rw [fixedSupport_adjoint_tensor]
  have hl (i : Fin n) : (∑ a ∈ supportLocalLabels (d := d) s i,
      (localWeylFin a).conjTranspose * P i * localWeylFin a) =
      (if i ∈ s then (d : ℂ)-1 else 1) • P i +
        (if i ∈ s then (d : ℂ) else 0) • (1-P i) := by
    by_cases hi : i ∈ s
    · simp only [supportLocalLabels, hi, ite_true]
      rw [localWeylFin_nonzero_readout (P i) (ht i)]
      module
    · simp [supportLocalLabels, hi]
  simp only [hl]
  rw [tensorMatrix_complement_expand]
  apply Finset.sum_congr rfl
  intro A _
  rw [← supportComplementCoefficient_eq]
  rfl

/-- Exact unnormalized shell expansion in physical complement tensors. -/
theorem weylShell_complement_expand [NeZero d] (j : ℕ)
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (ht : ∀ i, (P i).trace = 1) :
    (∑ u ∈ weylShell d n j,
      (quditWeyl u).conjTranspose * tensorMatrix P * quditWeyl u) =
      ∑ A : Finset (Fin n), (shellReadoutCoefficient d n j A.card : ℂ) •
        complementTensor P A := by
  have hf := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ (α := WeylLabel d n)) (Finset.univ.powersetCard j) weylSupport
    (fun u => (quditWeyl u).conjTranspose * tensorMatrix P * quditWeyl u)
  have hs : Finset.univ.filter (fun u : WeylLabel d n =>
      weylSupport u ∈ (Finset.univ : Finset (Fin n)).powersetCard j) = weylShell d n j := by
    unfold weylShell
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    exact Iff.rfl
  rw [hs] at hf
  rw [← hf]
  simp only [fixedSupport_complement_expand _ P ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [← Finset.sum_smul]
  congr 1
  simpa only [supportComplementCoefficient_eq] using supportComplementCoefficient_shell (d := d) j A

private theorem shell_complement_coefficient_sum (hd : 2 ≤ d) (j : ℕ) (hj : j ≤ n)
    (f : Finset (Fin n) → ℝ) :
    (((n.choose j * (d^2-1)^j : ℕ) : ℝ)⁻¹ *
      ∑ A : Finset (Fin n), shellReadoutCoefficient d n j A.card * f A) =
      (((d : ℝ)+1)⁻¹)^j * ∑ k ∈ Finset.range (j+1),
        (j.choose k : ℝ) * (d : ℝ)^k *
          (((n.choose k : ℝ) * ((d-1 : ℕ) : ℝ)^k)⁻¹ *
            ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f A) := by
  have hgroup : (∑ A : Finset (Fin n), shellReadoutCoefficient d n j A.card * f A) =
      ∑ k ∈ Finset.range (j+1), shellReadoutCoefficient d n j k *
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f A := by
    have hf := Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset (Finset (Fin n))) (Finset.range (j+1)) Finset.card
      (fun A => shellReadoutCoefficient d n j A.card * f A)
    have hc (k : ℕ) : Finset.univ.filter (fun A : Finset (Fin n) => A.card = k) =
        (Finset.univ : Finset (Fin n)).powersetCard k := by ext A; simp
    have he : (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) =>
        A.card ∈ Finset.range (j+1)), shellReadoutCoefficient d n j A.card * f A) =
        ∑ A : Finset (Fin n), shellReadoutCoefficient d n j A.card * f A := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A _ hA
      have hn : ¬ A.card ≤ j := by simpa using hA
      simp [shellReadoutCoefficient, hn]
    rw [he] at hf
    rw [← hf]
    apply Finset.sum_congr rfl
    intro k _
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [(Finset.mem_powersetCard.mp hA).2]
  rw [hgroup, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ j := by simpa using hk
  rw [← mul_assoc, shell_coefficient_normalized hd hj hk']
  ring

/-- SM IV's shell identity for every actual state and arbitrary trace-one local matrices. -/
theorem weylShell_complement_readout [NeZero d] (hd : 2 ≤ d)
    (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (ht : ∀ i, (P i).trace = 1)
    (j : ℕ) (hj : j ≤ n) :
    ((weylShellState hd ρ j hj).matrix * tensorMatrix P).trace.re =
      (((d : ℝ)+1)⁻¹)^j * ∑ k ∈ Finset.range (j+1),
        (j.choose k : ℝ) * (d : ℝ)^k * (ρ.matrix * complementRadius P k).trace.re := by
  have he := congrArg (fun B => (ρ.matrix * B).trace) (weylShell_complement_expand j P ht)
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul] at he
  rw [weylShellState_matrix]
  simp only [Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
    weyl_conjugate_pairing, he, Complex.smul_re, smul_eq_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [complementRadius, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re,
    smul_eq_mul, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  exact shell_complement_coefficient_sum hd j hj (fun A => (ρ.matrix * complementTensor P A).trace.re)

end LocalCertification.Quantum
