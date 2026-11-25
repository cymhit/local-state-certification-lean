import LocalCertification.Certificates.FairSearch

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Consumers

/-- A nonconstant exact optimal certificate, with the original positive nodes 1,2 and infinity. -/
def degreeOneCertificate : CertificateData 1 :=
  (1, ![18,-18], 2, ![some 0,some 1,none], ![6,-9,4])

theorem degreeOneCertificate_passes : certificateCheck 3 1 degreeOneCertificate=true := by
  unfold degreeOneCertificate
  norm_num [certificateCheck,arrayTailCheck,shiftArrayCoeff,
    arrayPrefixCheck,arrayEval,executableNodeMonomial,Fin.sum_univ_succ,Fin.forall_fin_succ]

theorem degree_one_exact_value : gamma 3 1=1/10 := by
  have h := (certificateCheck_sound 3 (by norm_num) 1 degreeOneCertificate degreeOneCertificate_passes).2.2
  norm_num [degreeOneCertificate,arrayEval,Fin.sum_univ_succ] at h ⊢
  exact h

theorem degree_one_search_finite : searchCertificateIndex 3 (by norm_num) 1≤
    Encodable.encode degreeOneCertificate+1 :=
  searchCertificateIndex_le 3 (by norm_num) 1 degreeOneCertificate degreeOneCertificate_passes

theorem degree_one_search_value :
    let c := searchCertificate 3 (by norm_num) 1
    ((2/(1+c.1+arrayEval 2 c.2.1 0) : ℚ) : ℝ)=1/10 := by
  have h := (certificateCheck_sound 3 (by norm_num) 1 _ (searchCertificate_passes 3 (by norm_num) 1)).2.2
  norm_num only [Rat.cast_ofNat] at h
  rw [degree_one_exact_value] at h
  exact h.symm

/-- Full candidate decision must reject a positive-leading tail whose finite prefix fails. -/
theorem infeasible_positive_tail_rejected :
    candidateCheck 3 (by norm_num) 0 (-1) (fun _ => 12)=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hf := (candidateCheck_correct 3 (by norm_num) 0 (-1) (fun _ => 12) (by norm_num)).mp h
  have hb := rationalCandidateValue_bound 3 0 (-1) (Polynomial.ofFn 1 (fun _ => 12))
    (by norm_num [Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_succ]) hf 1 (by omega)
  norm_num [rationalCandidateValue,weightedPolynomial,Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ] at hb

end LocalCertification.Certificates.Consumers
