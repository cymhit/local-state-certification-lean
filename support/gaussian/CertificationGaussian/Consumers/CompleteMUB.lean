import CertificationGaussian.CompleteMUBRemainder

noncomputable section
open MeasureTheory Matrix Metric Set
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- The three Pauli bases form a complete set of mutually unbiased qubit bases. -/
def actualPauliMUB : CompleteMUB 2 where
  basis := pauliBasisUnitary
  unbiased a b hab i j := by
    have hi : inner ℂ (pauliRecordedUnitVector (a,i)).val (pauliRecordedUnitVector (b,j)).val=
        ((pauliBasisMatrix a)ᴴ*pauliBasisMatrix b) i j := by
      simp only [PiLp.inner_apply,RCLike.inner_apply',Matrix.mul_apply,Matrix.conjTranspose_apply,
        pauliRecordedUnitVector_apply]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Complex.star_def]
    have h := pauli_record_overlap_sq (a,i) (b,j)
    simp only [recordOverlap,hi] at h
    simpa [hab,pauliBasisUnitary] using h

theorem actualPauliMUB_same_records :
    completeMUBRecords 2=pauliBasisRecords ∧
      completeMUBFullRecord actualPauliMUB=pauliFullRecord := ⟨rfl,rfl⟩

theorem actualPauliMUB_same_kappa :
    completeMUBStrictLoss 2=pauliStrictLoss ∧ completeMUBLocalKappa 2=pauliLocalKappa := by
  constructor
  · norm_num [completeMUBStrictLoss,completeMUBAmplitude,pauliStrictLoss]
    ring
  · unfold completeMUBLocalKappa pauliLocalKappa completeMUBStrictLoss completeMUBAmplitude pauliStrictLoss
    norm_num
    ring

/-- A nilpotent, non-Hermitian complex matrix exercises the fully linear twirl. -/
theorem actualPauliMUB_nilpotent_success :
    (2:ℂ)*(∫ ω,completeMUBProjector actualPauliMUB ω 0 1*
      Matrix.trace (completeMUBProjector actualPauliMUB ω*!![0,1;0,0])∂completeMUBRecords 2)=1/3 := by
  convert completeMUBRecords_success actualPauliMUB !![0,1;0,0] 0 1 using 1;
    norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem actualPauliMUB_strict_graph (g : FourVertexMultigraph)
    (hg : g.IsSixRegular) (hc : g.ContainsFourCycle) :
    0<completeMUBLocalKappa 2 ∧ completeMUBLocalKappa 2<1 ∧
      16*completeMUBFourOverlapIntegral actualPauliMUB g≤completeMUBLocalKappa 2 := by
  refine ⟨completeMUBLocalKappa_pos,completeMUBLocalKappa_lt_one (by decide),?_⟩
  convert completeMUBFourOverlapIntegral_scaled_le actualPauliMUB (by decide) g hg hc using 1; norm_num

/-- The conditional definition also has the correct one-dimensional, non-strict boundary. -/
def oneDimensionalMUB : CompleteMUB 1 where
  basis _ := 1
  unbiased b c hbc i j := by
    have hij : i=j := Subsingleton.elim _ _
    simp [hij]

theorem oneDimensionalMUB_twirl (A : Matrix (Fin 1) (Fin 1) ℂ) :
    (∫ ω,completeMUBProjector oneDimensionalMUB ω 0 0*
      Matrix.trace (completeMUBProjector oneDimensionalMUB ω*A)∂completeMUBRecords 1)=A 0 0 := by
  have h := completeMUBRecords_success oneDimensionalMUB A 0 0
  norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_one] at h
  simpa only [Matrix.trace,Matrix.diag,Fin.sum_univ_one] using h

theorem oneDimensionalMUB_kappa : completeMUBStrictLoss 1=0 ∧ completeMUBLocalKappa 1=1 := by
  norm_num [completeMUBStrictLoss,completeMUBAmplitude,completeMUBLocalKappa]

/-- Signed coefficients, the actual kernel, the same actual Gaussian and finite Pauli reference law. -/
theorem actualPauliMUB_signed_remainder (n : ℕ) :
    (∫ z,(Matrix.trace ((cardinalityReadoutRemainder (S:=Fin n) 2 (completeMUBRecords 2)
      (completeMUBFullRecord actualPauliMUB) 1 (fun j => if j=0 then 1 else -2)
        (complexCoordinate z))^4)).re∂pairedGaussian (QuditIndex 2 n))≤
      (Nat.factorial 8:ℝ)*16^8*
        (complementLambda 2 n 1 (fun j => if j=0 then 1 else -2))^8*
          (completeMUBLocalKappa 2)^(n-8) := by
  convert cardinalityMUB_remainder_bound (S:=Fin n) actualPauliMUB (by decide) 1
    (fun j => if j=0 then 1 else -2) using 1; norm_num

end CertificationGaussian.Consumers
