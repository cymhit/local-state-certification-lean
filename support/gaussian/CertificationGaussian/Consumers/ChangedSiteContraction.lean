import CertificationGaussian.ChangedSiteContraction

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Kronecker
namespace CertificationGaussian.Consumers

/-- A concrete non-involutive admissible permutation keeps both slots but cycles all four blocks. -/
def cycleBlockWickPermutation : Equiv.Perm (Fin 4 × Fin 2) :=
  Equiv.prodCongr outputTraceCycle (Equiv.refl (Fin 2))

theorem cycleBlockWickPermutation_admissible : cycleBlockWickPermutation∈fourBlockDerangements := by
  simp only [fourBlockDerangements,Finset.mem_filter,Finset.mem_univ,true_and]
  rintro ⟨b,a⟩
  fin_cases b <;> fin_cases a <;> decide

theorem cycleBlockWickPermutation_not_inverse :
    cycleBlockWickPermutation≠cycleBlockWickPermutation.symm := by
  intro h
  have ht := congrArg (fun e : Equiv.Perm (Fin 4 × Fin 2) => (e (0,0)).1) h
  change (3:Fin 4)=1 at ht
  norm_num at ht

/-- With no input complement, the contraction reduces to the Haar unchanged-site integrand. -/
theorem haar_all_projectors (d : ℕ) [NeZero d] (π : Equiv.Perm (Fin 4 × Fin 2)) :
    haarChangedSiteIntegrand d (fun _ => false) π=haarUnchangedSiteIntegrand d π := rfl

theorem pauli_all_projectors (π : Equiv.Perm (Fin 4 × Fin 2)) :
    pauliChangedSiteIntegrand (fun _ => false) π=pauliUnchangedSiteIntegrand π := rfl

/-- Qutrit input choices are arbitrary; no forbidden-pairing or positivity premise is needed for the changed-site cost. -/
theorem actual_qutrit_changed_site (a : Fin 4 × Fin 2 → Bool)
    (π : Equiv.Perm (Fin 4 × Fin 2)) :
    ‖(81:ℂ)*(∫ x,haarChangedSiteIntegrand 3 a π x ∂fourReadoutLaw (haarBasisRecords 3))‖≤20736 := by
  have h := haarChangedSiteContraction_le 3 (by decide) a π
  norm_num at h ⊢
  exact h

/-- A genuinely mixed P/(I-P) Pauli contraction, with a non-self-inverse Wick permutation. -/
theorem actual_mixed_pauli_changed_site :
    ‖(16:ℂ)*(∫ x,pauliChangedSiteIntegrand (fun t => decide (t.2=1))
      cycleBlockWickPermutation x ∂fourReadoutLaw pauliBasisRecords)‖≤16 :=
  pauliChangedSiteContraction_le _ _

/-- In the unchanged specialization the very same integral has the strict κ bound. -/
theorem actual_unchanged_pauli_strict :
    ‖(16:ℂ)*(∫ x,pauliChangedSiteIntegrand (fun _ => false)
      cycleBlockWickPermutation x ∂fourReadoutLaw pauliBasisRecords)‖≤pauliLocalKappa := by
  rw [pauli_all_projectors]
  exact pauliUnchangedSiteContraction_le _ cycleBlockWickPermutation_admissible

/-- Empty base coordinates leave an empty actual twelve-slot operator; its unitary law is still valid. -/
theorem empty_combined_operator (π : Equiv.Perm (Fin 4 × Fin 2)) :
    combinedWickPermutationMatrix (I:=Fin 0) π=0 ∧
      combinedWickPermutationMatrix (I:=Fin 0) π∈unitary _ := by
  constructor
  · ext x y
    exact Fin.elim0 (x 0).1.1
  · exact combinedWickPermutationMatrix_unitary π

end CertificationGaussian.Consumers
