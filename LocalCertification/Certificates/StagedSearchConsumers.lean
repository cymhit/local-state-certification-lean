import LocalCertification.Certificates.StagedSearch
import LocalCertification.Certificates.CanonicalCertificateConsumers
import LocalCertification.Certificates.Examples.Degree2
import LocalCertification.Certificates.Examples.Degree10

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Consumers

theorem staged_degree_zero_bound : stagedSearchIndex 3 (by norm_num) 0≤6 := by
  have h := stagedSearchIndex_le 3 (by norm_num) 0 _ canonical_degree_zero_passes
  apply h.trans
  norm_num [stagedDataBound,seedCertificate,Finset.sup_le_iff,Fin.forall_fin_succ]

theorem staged_degree_one_bound : stagedSearchIndex 3 (by norm_num) 1≤18 := by
  have h := stagedSearchIndex_le 3 (by norm_num) 1 _ canonical_degree_one_passes
  apply h.trans
  norm_num [stagedDataBound,degreeOneCertificate,Finset.sup_le_iff,Fin.forall_fin_succ]

theorem staged_degree_two_raw_passes : canonicalRawCheck 3 2 Examples.Degree2.data=true := by
  unfold Examples.Degree2.data
  norm_num [canonicalRawCheck,canonicalRawCandidateCheck,canonicalNodeLt,canonicalRawValue,canonicalRawQ,canonicalParity,
    arrayTailCheck,shiftArrayCoeff,arrayPrefixCheck,arrayEval,executableNodeMonomial,
    Fin.sum_univ_succ,Fin.forall_fin_succ,Fin.last]

theorem staged_degree_two_bound : stagedSearchIndex 3 (by norm_num) 2≤93 := by
  have h := stagedSearchIndex_le 3 (by norm_num) 2 _ staged_degree_two_raw_passes
  apply h.trans
  norm_num [stagedDataBound,Examples.Degree2.data,Finset.sup_le_iff,Fin.forall_fin_succ]

theorem staged_degree_zero_value :
    let d := stagedSearch 3 (by norm_num) 0
    ((2/(1+∑ i, |d.2.2.2.2 i|) : ℚ) : ℝ)=1/3 := by
  exact (stagedSearch_correct 3 (by norm_num) 0).2.1.symm.trans canonical_degree_zero_value

theorem staged_degree_one_value :
    let d := stagedSearch 3 (by norm_num) 1
    ((2/(1+∑ i, |d.2.2.2.2 i|) : ℚ) : ℝ)=1/10 := by
  exact (stagedSearch_correct 3 (by norm_num) 1).2.1.symm.trans canonical_degree_one_value

/-- Coverage of the degree-ten table row is proved from its finite data; the stage is not run. -/
theorem staged_degree_ten_covered :
    Examples.Degree10.data ∈ stagedData 10 218193293112653 := by
  apply (mem_stagedData _ _ _).mpr
  refine ⟨by norm_num [Examples.Degree10.data,canonicalParity],
    by norm_num [Examples.Degree10.data],by norm_num [Examples.Degree10.data],?_,?_,?_⟩
  · apply (mem_stagedNodes _ _ _).mpr
    norm_num [Examples.Degree10.data,Fin.forall_fin_succ,canonicalNodeLt,Fin.last]
  · intro i
    apply mem_stagedRationals
    · fin_cases i <;> norm_num [Examples.Degree10.data]
    · fin_cases i <;> norm_num [Examples.Degree10.data]
  · intro i
    apply mem_stagedRationals
    · fin_cases i <;> norm_num [Examples.Degree10.data]
    · fin_cases i <;> norm_num [Examples.Degree10.data]

end LocalCertification.Certificates.Consumers
