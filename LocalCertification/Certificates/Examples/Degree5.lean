import LocalCertification.Certificates.SearchConsumers

set_option autoImplicit false
open scoped BigOperators
open Polynomial LocalCertification.Extremal
namespace LocalCertification.Certificates.Examples.Degree5

def data : CertificateData 5 :=
  (1,![(77274/35),(-166779/35),(100845/28),(-68463/56),(26469/140),(-3033/280)],9,![some 0,some 1,some 2,some 3,some 5,some 8,none],![(81/5),(-729/7),(324),(-2187/5),(2187/5),(-19683/35),(11456/35)])

theorem tail_0 : 0≤shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 0 ∧
    0≤3*shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 0-shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 10 0 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_1 : 0≤shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 1 ∧
    0≤3*shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 1-shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 10 1 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_2 : 0≤shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 2 ∧
    0≤3*shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 2-shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 10 2 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_3 : 0≤shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 3 ∧
    0≤3*shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 3-shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 10 3 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_4 : 0≤shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 4 ∧
    0≤3*shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 4-shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 10 4 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem tail_5 : 0≤shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 5 ∧
    0≤3*shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 9 5-shiftArrayCoeff 6 (fun i => -data.1*data.2.1 i) 10 5 := by
  norm_num [data,shiftArrayCoeff,Fin.sum_univ_succ,Nat.choose]

theorem prefix_1 : |data.1+(3 : ℚ)⁻¹^1*arrayEval 6 data.2.1 1|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_2 : |data.1+(3 : ℚ)⁻¹^2*arrayEval 6 data.2.1 2|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_3 : |data.1+(3 : ℚ)⁻¹^3*arrayEval 6 data.2.1 3|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_4 : |data.1+(3 : ℚ)⁻¹^4*arrayEval 6 data.2.1 4|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_5 : |data.1+(3 : ℚ)⁻¹^5*arrayEval 6 data.2.1 5|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_6 : |data.1+(3 : ℚ)⁻¹^6*arrayEval 6 data.2.1 6|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_7 : |data.1+(3 : ℚ)⁻¹^7*arrayEval 6 data.2.1 7|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_8 : |data.1+(3 : ℚ)⁻¹^8*arrayEval 6 data.2.1 8|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem prefix_9 : |data.1+(3 : ℚ)⁻¹^9*arrayEval 6 data.2.1 9|≤1 := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem moment_0 : (∑ i : Fin 7, data.2.2.2.2 i*executableNodeMonomial 3 0 (data.2.2.2.1 i))=(0 : ℚ)^0 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_1 : (∑ i : Fin 7, data.2.2.2.2 i*executableNodeMonomial 3 1 (data.2.2.2.1 i))=(0 : ℚ)^1 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_2 : (∑ i : Fin 7, data.2.2.2.2 i*executableNodeMonomial 3 2 (data.2.2.2.1 i))=(0 : ℚ)^2 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_3 : (∑ i : Fin 7, data.2.2.2.2 i*executableNodeMonomial 3 3 (data.2.2.2.1 i))=(0 : ℚ)^3 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_4 : (∑ i : Fin 7, data.2.2.2.2 i*executableNodeMonomial 3 4 (data.2.2.2.1 i))=(0 : ℚ)^4 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem moment_5 : (∑ i : Fin 7, data.2.2.2.2 i*executableNodeMonomial 3 5 (data.2.2.2.1 i))=(0 : ℚ)^5 := by
  norm_num [data,executableNodeMonomial,Fin.sum_univ_succ]

theorem tail_passes : arrayTailCheck 3 6 (fun i => -data.1*data.2.1 i) 9=true := by
  apply decide_eq_true
  intro k
  fin_cases k
  · exact tail_0
  · exact tail_1
  · exact tail_2
  · exact tail_3
  · exact tail_4
  · exact tail_5

theorem prefix_passes : arrayPrefixCheck 3 data.1 6 data.2.1 9=true := by
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

theorem mass : (∑ i : Fin 7, data.2.2.2.2 i)=1 := by
  norm_num [data,Fin.sum_univ_succ]

theorem norm_match : data.1+arrayEval 6 data.2.1 0=∑ i : Fin 7, |data.2.2.2.2 i| := by
  norm_num [data,arrayEval,Fin.sum_univ_succ]

theorem certificate_passes : certificateCheck 3 5 data=true := by
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

theorem exact_value : gamma 3 5=35/38672 := by
  have h := (certificateCheck_sound 3 (by norm_num) 5 data certificate_passes).2.2
  norm_num [data,arrayEval,Fin.sum_univ_succ] at h ⊢
  exact h

end LocalCertification.Certificates.Examples.Degree5
