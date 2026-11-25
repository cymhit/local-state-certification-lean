import LocalCertification.Certificates.SearchConsumers

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Examples.Degree2

def data : CertificateData 2 :=
  (-1,![(70),(-93),(29)],4,![some 0,some 1,some 3,none],![(8),(-18),(27),(-16)])

theorem tail_0 : 0≤shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 4 0 ∧
    0≤3*shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 4 0-shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 5 0 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ]

theorem tail_1 : 0≤shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 4 1 ∧
    0≤3*shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 4 1-shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 5 1 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ]

theorem tail_2 : 0≤shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 4 2 ∧
    0≤3*shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 4 2-shiftArrayCoeff 3 (fun i => -data.1*data.2.1 i) 5 2 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ]

theorem prefix_1 : |data.1+(3 : ℚ)⁻¹^1*arrayEval 3 data.2.1 1|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_2 : |data.1+(3 : ℚ)⁻¹^2*arrayEval 3 data.2.1 2|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_3 : |data.1+(3 : ℚ)⁻¹^3*arrayEval 3 data.2.1 3|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_4 : |data.1+(3 : ℚ)⁻¹^4*arrayEval 3 data.2.1 4|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem moment_0 : (∑ i : Fin 4, data.2.2.2.2 i*executableNodeMonomial 3 0 (data.2.2.2.1 i))=(0 : ℚ)^0 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_1 : (∑ i : Fin 4, data.2.2.2.2 i*executableNodeMonomial 3 1 (data.2.2.2.1 i))=(0 : ℚ)^1 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_2 : (∑ i : Fin 4, data.2.2.2.2 i*executableNodeMonomial 3 2 (data.2.2.2.1 i))=(0 : ℚ)^2 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem tail_passes : arrayTailCheck 3 3 (fun i => -data.1*data.2.1 i) 4=true := by
  apply decide_eq_true
  intro k
  fin_cases k
  · exact tail_0
  · exact tail_1
  · exact tail_2

theorem prefix_passes : arrayPrefixCheck 3 data.1 3 data.2.1 4=true := by
  apply decide_eq_true
  intro w
  fin_cases w
  · exact prefix_1
  · exact prefix_2
  · exact prefix_3
  · exact prefix_4

theorem mass : (∑ i : Fin 4, data.2.2.2.2 i)=1 := by
  norm_num [data,Fin.sum_univ_succ]

theorem norm_match : data.1+arrayEval 3 data.2.1 0=∑ i : Fin 4, |data.2.2.2.2 i| := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem certificate_passes : certificateCheck 3 2 data=true := by
  apply decide_eq_true
  refine ⟨by norm_num [data],by norm_num [data],tail_passes,prefix_passes,mass,?_,norm_match⟩
  intro j
  fin_cases j
  · exact moment_0
  · exact moment_1
  · exact moment_2

theorem exact_value : gamma 3 2=1/35 := by
  have h := (certificateCheck_sound 3 (by norm_num) 2 data certificate_passes).2.2
  norm_num [data,arrayEval,Fin.sum_univ_succ] at h ⊢
  exact h

end LocalCertification.Certificates.Examples.Degree2
