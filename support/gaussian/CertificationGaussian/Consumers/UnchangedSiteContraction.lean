import CertificationGaussian.UnchangedSiteContraction

noncomputable section
open MeasureTheory Matrix Metric Set
namespace CertificationGaussian.Consumers

/-- A concrete admissible Wick permutation swaps whole blocks in two pairs and preserves both slots. -/
def pairedBlockWickPermutation : Equiv.Perm (Fin 4 × Fin 2) :=
  Equiv.prodCongr ((Equiv.swap (0:Fin 4) 1)*(Equiv.swap (2:Fin 4) 3)) (Equiv.refl (Fin 2))

theorem pairedBlockWickPermutation_admissible : pairedBlockWickPermutation∈fourBlockDerangements := by
  simp only [fourBlockDerangements,Finset.mem_filter,Finset.mem_univ,true_and]
  rintro ⟨b,a⟩
  fin_cases b <;> fin_cases a <;> decide

/-- The actual permutation has eight Wick edges; after adding the output cycle its multiplicities
are 5,0,1,1,0,5, not a simple graph or an ordinary fixed-point derangement. -/
theorem pairedBlockWickPermutation_multiplicities :
    (wickFourVertexGraph pairedBlockWickPermutation).e01=5 ∧
    (wickFourVertexGraph pairedBlockWickPermutation).e02=0 ∧
    (wickFourVertexGraph pairedBlockWickPermutation).e03=1 ∧
    (wickFourVertexGraph pairedBlockWickPermutation).e12=1 ∧
    (wickFourVertexGraph pairedBlockWickPermutation).e13=0 ∧
    (wickFourVertexGraph pairedBlockWickPermutation).e23=5 := by decide

/-- Every true Haar unchanged-site matrix term has the same strict dimension-only bound. -/
theorem actual_haar_unchanged_site (d : ℕ) [NeZero d] (hd : 3≤d) :
    0<haarLocalKappa d ∧ haarLocalKappa d<1 ∧
    ∀ π : Equiv.Perm (Fin 4 × Fin 2), π∈fourBlockDerangements →
      ‖(d:ℂ)^4*∫ x,haarUnchangedSiteIntegrand d π x ∂fourReadoutLaw (haarBasisRecords d)‖≤haarLocalKappa d :=
  ⟨haarLocalKappa_pos d (by omega),haarLocalKappa_lt_one d hd,
    fun π hπ => haarUnchangedSiteContraction_le d π hπ⟩

/-- The same actual matrix terms on the finite Pauli ensemble have a strict common bound. -/
theorem actual_pauli_unchanged_site :
    0<pauliLocalKappa ∧ pauliLocalKappa<1 ∧
    ∀ π : Equiv.Perm (Fin 4 × Fin 2), π∈fourBlockDerangements →
      ‖(16:ℂ)*∫ x,pauliUnchangedSiteIntegrand π x ∂fourReadoutLaw pauliBasisRecords‖≤pauliLocalKappa :=
  ⟨pauliLocalKappa_pos,pauliLocalKappa_lt_one,fun π hπ => pauliUnchangedSiteContraction_le π hπ⟩

theorem concrete_pauli_wick_term :
    ‖(16:ℂ)*∫ x,pauliUnchangedSiteIntegrand pairedBlockWickPermutation x
      ∂fourReadoutLaw pauliBasisRecords‖≤pauliLocalKappa :=
  pauliUnchangedSiteContraction_le _ pairedBlockWickPermutation_admissible

theorem concrete_haar_qutrit_wick_term :
    ‖(81:ℂ)*∫ x,haarUnchangedSiteIntegrand 3 pairedBlockWickPermutation x
      ∂fourReadoutLaw (haarBasisRecords 3)‖≤(81/100:ℝ) := by
  have h := haarUnchangedSiteContraction_le 3 pairedBlockWickPermutation pairedBlockWickPermutation_admissible
  norm_num [haarLocalKappa] at h ⊢
  exact h

/-- Empty tensor slots give the actual one-dimensional tensor identity, even with empty base coordinates. -/
theorem empty_rankone_wick_slots (v : Fin 0 → EuclideanSpace ℂ (Fin 0)) :
    Matrix.trace (wickTensorMatrix (fun t => vectorRankOne (v t) (v t))*
      wickTensorPermutationMatrix (Equiv.refl (Fin 0)))=1 := by
  rw [vectorRankOne_wick_trace]
  exact Fin.prod_univ_zero _

end CertificationGaussian.Consumers
