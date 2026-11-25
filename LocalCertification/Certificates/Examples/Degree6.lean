import LocalCertification.Certificates.SearchConsumers

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Examples.Degree6

def data : CertificateData 6 :=
  (-1,![(27667/4),(-27033137/1680),(46228787/3360),(-474931/84),(401591/336),(-209123/1680),(16943/3360)],11,![some 0,some 1,some 2,some 3,some 4,some 6,some 10,none],![(77/4),(-154),(10395/16),(-1485),(6237/4),(-8019/8),(19683/16),(-816)])

theorem tail_0 : 0≤shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 0 ∧
    0≤3*shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 0-shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 12 0 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_1 : 0≤shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 1 ∧
    0≤3*shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 1-shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 12 1 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_2 : 0≤shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 2 ∧
    0≤3*shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 2-shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 12 2 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_3 : 0≤shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 3 ∧
    0≤3*shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 3-shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 12 3 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_4 : 0≤shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 4 ∧
    0≤3*shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 4-shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 12 4 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_5 : 0≤shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 5 ∧
    0≤3*shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 5-shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 12 5 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_6 : 0≤shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 6 ∧
    0≤3*shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 11 6-shiftArrayCoeff 7 (fun i => -data.1*data.2.1 i) 12 6 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem prefix_1 : |data.1+(3 : ℚ)⁻¹^1*arrayEval 7 data.2.1 1|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_2 : |data.1+(3 : ℚ)⁻¹^2*arrayEval 7 data.2.1 2|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_3 : |data.1+(3 : ℚ)⁻¹^3*arrayEval 7 data.2.1 3|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_4 : |data.1+(3 : ℚ)⁻¹^4*arrayEval 7 data.2.1 4|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_5 : |data.1+(3 : ℚ)⁻¹^5*arrayEval 7 data.2.1 5|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_6 : |data.1+(3 : ℚ)⁻¹^6*arrayEval 7 data.2.1 6|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_7 : |data.1+(3 : ℚ)⁻¹^7*arrayEval 7 data.2.1 7|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_8 : |data.1+(3 : ℚ)⁻¹^8*arrayEval 7 data.2.1 8|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_9 : |data.1+(3 : ℚ)⁻¹^9*arrayEval 7 data.2.1 9|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_10 : |data.1+(3 : ℚ)⁻¹^10*arrayEval 7 data.2.1 10|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_11 : |data.1+(3 : ℚ)⁻¹^11*arrayEval 7 data.2.1 11|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem moment_0 : (∑ i : Fin 8, data.2.2.2.2 i*executableNodeMonomial 3 0 (data.2.2.2.1 i))=(0 : ℚ)^0 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_1 : (∑ i : Fin 8, data.2.2.2.2 i*executableNodeMonomial 3 1 (data.2.2.2.1 i))=(0 : ℚ)^1 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_2 : (∑ i : Fin 8, data.2.2.2.2 i*executableNodeMonomial 3 2 (data.2.2.2.1 i))=(0 : ℚ)^2 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_3 : (∑ i : Fin 8, data.2.2.2.2 i*executableNodeMonomial 3 3 (data.2.2.2.1 i))=(0 : ℚ)^3 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_4 : (∑ i : Fin 8, data.2.2.2.2 i*executableNodeMonomial 3 4 (data.2.2.2.1 i))=(0 : ℚ)^4 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_5 : (∑ i : Fin 8, data.2.2.2.2 i*executableNodeMonomial 3 5 (data.2.2.2.1 i))=(0 : ℚ)^5 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_6 : (∑ i : Fin 8, data.2.2.2.2 i*executableNodeMonomial 3 6 (data.2.2.2.1 i))=(0 : ℚ)^6 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem tail_passes : arrayTailCheck 3 7 (fun i => -data.1*data.2.1 i) 11=true := by
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

theorem prefix_passes : arrayPrefixCheck 3 data.1 7 data.2.1 11=true := by
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

theorem mass : (∑ i : Fin 8, data.2.2.2.2 i)=1 := by
  norm_num [data,Fin.sum_univ_succ]

theorem norm_match : data.1+arrayEval 7 data.2.1 0=∑ i : Fin 8, |data.2.2.2.2 i| := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem certificate_passes : certificateCheck 3 6 data=true := by
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

theorem exact_value : gamma 3 6=8/27667 := by
  have h := (certificateCheck_sound 3 (by norm_num) 6 data certificate_passes).2.2
  norm_num [data,arrayEval,Fin.sum_univ_succ] at h ⊢
  exact h

end LocalCertification.Certificates.Examples.Degree6
