import LocalCertification.Certificates.SearchConsumers

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Examples.Degree9

def data : CertificateData 9 :=
  (1,![(1079329698/5005),(-409608579969/700700),(50420959839/80080),(-40408849395/112112),(5599142643/45760),(-20635109493/800800),(542598597/160160),(-7552473/28028),(3783957/320320),(-1223847/5605600)],16,![some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 8,some 11,some 15,none],![(1512/55),(-11664/35),(30240/13),(-10206),(314928/11),(-244944/5),(209952/5),(-157464/7),(1062882/55),(-129140163/5005),(77713408/5005)])

theorem tail_0 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 0 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 0-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 0 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_1 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 1 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 1-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 1 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_2 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 2 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 2-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 2 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_3 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 3 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 3-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 3 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_4 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 4 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 4-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 4 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_5 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 5 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 5-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 5 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_6 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 6 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 6-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 6 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_7 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 7 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 7-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 7 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_8 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 8 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 8-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 8 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_9 : 0≤shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 9 ∧
    0≤3*shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 16 9-shiftArrayCoeff 10 (fun i => -data.1*data.2.1 i) 17 9 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem prefix_1 : |data.1+(3 : ℚ)⁻¹^1*arrayEval 10 data.2.1 1|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_2 : |data.1+(3 : ℚ)⁻¹^2*arrayEval 10 data.2.1 2|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_3 : |data.1+(3 : ℚ)⁻¹^3*arrayEval 10 data.2.1 3|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_4 : |data.1+(3 : ℚ)⁻¹^4*arrayEval 10 data.2.1 4|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_5 : |data.1+(3 : ℚ)⁻¹^5*arrayEval 10 data.2.1 5|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_6 : |data.1+(3 : ℚ)⁻¹^6*arrayEval 10 data.2.1 6|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_7 : |data.1+(3 : ℚ)⁻¹^7*arrayEval 10 data.2.1 7|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_8 : |data.1+(3 : ℚ)⁻¹^8*arrayEval 10 data.2.1 8|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_9 : |data.1+(3 : ℚ)⁻¹^9*arrayEval 10 data.2.1 9|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_10 : |data.1+(3 : ℚ)⁻¹^10*arrayEval 10 data.2.1 10|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_11 : |data.1+(3 : ℚ)⁻¹^11*arrayEval 10 data.2.1 11|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_12 : |data.1+(3 : ℚ)⁻¹^12*arrayEval 10 data.2.1 12|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_13 : |data.1+(3 : ℚ)⁻¹^13*arrayEval 10 data.2.1 13|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_14 : |data.1+(3 : ℚ)⁻¹^14*arrayEval 10 data.2.1 14|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_15 : |data.1+(3 : ℚ)⁻¹^15*arrayEval 10 data.2.1 15|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_16 : |data.1+(3 : ℚ)⁻¹^16*arrayEval 10 data.2.1 16|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem moment_0 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 0 (data.2.2.2.1 i))=(0 : ℚ)^0 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_1 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 1 (data.2.2.2.1 i))=(0 : ℚ)^1 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_2 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 2 (data.2.2.2.1 i))=(0 : ℚ)^2 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_3 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 3 (data.2.2.2.1 i))=(0 : ℚ)^3 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_4 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 4 (data.2.2.2.1 i))=(0 : ℚ)^4 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_5 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 5 (data.2.2.2.1 i))=(0 : ℚ)^5 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_6 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 6 (data.2.2.2.1 i))=(0 : ℚ)^6 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_7 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 7 (data.2.2.2.1 i))=(0 : ℚ)^7 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_8 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 8 (data.2.2.2.1 i))=(0 : ℚ)^8 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_9 : (∑ i : Fin 11, data.2.2.2.2 i*executableNodeMonomial 3 9 (data.2.2.2.1 i))=(0 : ℚ)^9 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem tail_passes : arrayTailCheck 3 10 (fun i => -data.1*data.2.1 i) 16=true := by
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
  · exact tail_8
  · exact tail_9

theorem prefix_passes : arrayPrefixCheck 3 data.1 10 data.2.1 16=true := by
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
  · exact prefix_14
  · exact prefix_15
  · exact prefix_16

theorem mass : (∑ i : Fin 11, data.2.2.2.2 i)=1 := by
  norm_num [data,Fin.sum_univ_succ]

theorem norm_match : data.1+arrayEval 10 data.2.1 0=∑ i : Fin 11, |data.2.2.2.2 i| := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem certificate_passes : certificateCheck 3 9 data=true := by
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
  · exact moment_8
  · exact moment_9

theorem exact_value : gamma 3 9=5005/539669854 := by
  have h := (certificateCheck_sound 3 (by norm_num) 9 data certificate_passes).2.2
  norm_num [data,arrayEval,Fin.sum_univ_succ] at h ⊢
  exact h

end LocalCertification.Certificates.Examples.Degree9
