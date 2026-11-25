import LocalCertification.Certificates.CanonicalRawCheck
import LocalCertification.Certificates.SearchConsumers

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Consumers

theorem canonical_degree_zero_passes : canonicalRawCheck 3 0 (seedCertificate 3 0)=true := by
  unfold seedCertificate
  norm_num [canonicalRawCheck,canonicalRawCandidateCheck,canonicalNodeLt,canonicalRawValue,canonicalRawQ,canonicalParity,
    seedCertificate,degreeOneCertificate,arrayTailCheck,shiftArrayCoeff,arrayPrefixCheck,
    arrayEval,executableNodeMonomial,Fin.sum_univ_succ,Fin.forall_fin_succ,Fin.last]

theorem canonical_degree_one_passes : canonicalRawCheck 3 1 degreeOneCertificate=true := by
  unfold degreeOneCertificate
  norm_num [canonicalRawCheck,canonicalRawCandidateCheck,canonicalNodeLt,canonicalRawValue,canonicalRawQ,canonicalParity,
    seedCertificate,degreeOneCertificate,arrayTailCheck,shiftArrayCoeff,arrayPrefixCheck,
    arrayEval,executableNodeMonomial,Fin.sum_univ_succ,Fin.forall_fin_succ,Fin.last]

theorem canonical_degree_zero_value : gamma 3 0=1/3 := by
  have h := (canonicalRawCheck_optimality 3 (by norm_num) 0 _ canonical_degree_zero_passes).2.1
  norm_num [seedCertificate,Fin.sum_univ_succ] at h ⊢
  exact h

theorem canonical_degree_one_value : gamma 3 1=1/10 := by
  have h := (canonicalRawCheck_optimality 3 (by norm_num) 1 _ canonical_degree_one_passes).2.1
  norm_num [degreeOneCertificate,Fin.sum_univ_succ] at h ⊢
  exact h

end LocalCertification.Certificates.Consumers
