import LocalCertification.Certificates.SearchConsumers

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Examples.Degree7

def data : CertificateData 7 :=
  (1,![(13931433/616),(-689007357/12320),(18493245/352),(-3175815/128),(412539/64),(-1636629/1760),(342267/4928),(-20565/9856)],13,![some 0,some 1,some 2,some 3,some 4,some 5,some 8,some 12,none],![(351/16),(-15795/77),(1053),(-3159),(85293/16),(-28431/7),(255879/112),(-4782969/1232),(201632/77)])

theorem tail_0 : 0≤shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 0 ∧
    0≤3*shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 0-shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 14 0 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_1 : 0≤shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 1 ∧
    0≤3*shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 1-shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 14 1 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_2 : 0≤shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 2 ∧
    0≤3*shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 2-shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 14 2 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_3 : 0≤shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 3 ∧
    0≤3*shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 3-shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 14 3 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_4 : 0≤shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 4 ∧
    0≤3*shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 4-shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 14 4 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_5 : 0≤shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 5 ∧
    0≤3*shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 5-shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 14 5 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_6 : 0≤shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 6 ∧
    0≤3*shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 6-shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 14 6 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_7 : 0≤shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 7 ∧
    0≤3*shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 13 7-shiftArrayCoeff 8 (fun i => -data.1*data.2.1 i) 14 7 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem prefix_1 : |data.1+(3 : ℚ)⁻¹^1*arrayEval 8 data.2.1 1|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_2 : |data.1+(3 : ℚ)⁻¹^2*arrayEval 8 data.2.1 2|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_3 : |data.1+(3 : ℚ)⁻¹^3*arrayEval 8 data.2.1 3|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_4 : |data.1+(3 : ℚ)⁻¹^4*arrayEval 8 data.2.1 4|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_5 : |data.1+(3 : ℚ)⁻¹^5*arrayEval 8 data.2.1 5|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_6 : |data.1+(3 : ℚ)⁻¹^6*arrayEval 8 data.2.1 6|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_7 : |data.1+(3 : ℚ)⁻¹^7*arrayEval 8 data.2.1 7|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_8 : |data.1+(3 : ℚ)⁻¹^8*arrayEval 8 data.2.1 8|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_9 : |data.1+(3 : ℚ)⁻¹^9*arrayEval 8 data.2.1 9|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_10 : |data.1+(3 : ℚ)⁻¹^10*arrayEval 8 data.2.1 10|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_11 : |data.1+(3 : ℚ)⁻¹^11*arrayEval 8 data.2.1 11|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_12 : |data.1+(3 : ℚ)⁻¹^12*arrayEval 8 data.2.1 12|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_13 : |data.1+(3 : ℚ)⁻¹^13*arrayEval 8 data.2.1 13|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem moment_0 : (∑ i : Fin 9, data.2.2.2.2 i*executableNodeMonomial 3 0 (data.2.2.2.1 i))=(0 : ℚ)^0 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_1 : (∑ i : Fin 9, data.2.2.2.2 i*executableNodeMonomial 3 1 (data.2.2.2.1 i))=(0 : ℚ)^1 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_2 : (∑ i : Fin 9, data.2.2.2.2 i*executableNodeMonomial 3 2 (data.2.2.2.1 i))=(0 : ℚ)^2 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_3 : (∑ i : Fin 9, data.2.2.2.2 i*executableNodeMonomial 3 3 (data.2.2.2.1 i))=(0 : ℚ)^3 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_4 : (∑ i : Fin 9, data.2.2.2.2 i*executableNodeMonomial 3 4 (data.2.2.2.1 i))=(0 : ℚ)^4 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_5 : (∑ i : Fin 9, data.2.2.2.2 i*executableNodeMonomial 3 5 (data.2.2.2.1 i))=(0 : ℚ)^5 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_6 : (∑ i : Fin 9, data.2.2.2.2 i*executableNodeMonomial 3 6 (data.2.2.2.1 i))=(0 : ℚ)^6 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_7 : (∑ i : Fin 9, data.2.2.2.2 i*executableNodeMonomial 3 7 (data.2.2.2.1 i))=(0 : ℚ)^7 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem tail_passes : arrayTailCheck 3 8 (fun i => -data.1*data.2.1 i) 13=true := by
  apply decide_eq_true
  intro k
  fin_cases k
  · exact tail_0
  · exact tail_1
  · exact tail_2
  · exact tail_3
  · exact tail_4
  · exact tail_5
  · exact tail_6
  · exact tail_7

theorem prefix_passes : arrayPrefixCheck 3 data.1 8 data.2.1 13=true := by
  apply decide_eq_true
  intro w
  fin_cases w
  · exact prefix_1
  · exact prefix_2
  · exact prefix_3
  · exact prefix_4
  · exact prefix_5
  · exact prefix_6
  · exact prefix_7
  · exact prefix_8
  · exact prefix_9
  · exact prefix_10
  · exact prefix_11
  · exact prefix_12
  · exact prefix_13

theorem mass : (∑ i : Fin 9, data.2.2.2.2 i)=1 := by
  norm_num [data,Fin.sum_univ_succ]

theorem norm_match : data.1+arrayEval 8 data.2.1 0=∑ i : Fin 9, |data.2.2.2.2 i| := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem certificate_passes : certificateCheck 3 7 data=true := by
  apply decide_eq_true
  refine ⟨by norm_num [data],by norm_num [data],tail_passes,prefix_passes,mass,?_,norm_match⟩
  intro j
  fin_cases j
  · exact moment_0
  · exact moment_1
  · exact moment_2
  · exact moment_3
  · exact moment_4
  · exact moment_5
  · exact moment_6
  · exact moment_7

theorem exact_value : gamma 3 7=1232/13932665 := by
  have h := (certificateCheck_sound 3 (by norm_num) 7 data certificate_passes).2.2
  norm_num [data,arrayEval,Fin.sum_univ_succ] at h ⊢
  exact h

end LocalCertification.Certificates.Examples.Degree7
