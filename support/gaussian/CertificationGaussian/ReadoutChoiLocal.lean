import CertificationGaussian.CardinalityReadoutMoments
import CertificationGaussian.RadialBellChoi

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- Bell input/output ordering, with its actual dimension normalization. -/
theorem unitaryBellProjector_entry {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (i a j b : I) :
    unitaryBellProjector U (i,a) (j,b)=
      (Fintype.card I:ℂ)⁻¹*(U a i*star (U b j)) := by
  have h := congrArg (fun M : Matrix (I×I) (I×I) ℂ => M (j,a) (i,b))
    (unitaryBellProjector_partialTranspose U)
  exact h

/-- The local success Choi entry, derived from the previously fixed normalized Bell projector. -/
theorem radialChoiA0_entry (d : ℕ) (hd : 0<d) (i a j b : Fin d) :
    radialChoiA0 d (i,a) (j,b)=
      ((if a=i ∧ b=j then 1 else 0)+(if i=j ∧ a=b then 1 else 0))/(d+1:ℂ) := by
  have hd0 : (d:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hd
  have hq0 : (d+1:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt (Nat.succ_pos d)
  simp only [radialChoiA0,radialChoiPhi,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,unitaryBellProjector_entry,Fintype.card_fin,Matrix.one_apply,Prod.mk.injEq]
  by_cases h1 : a=i <;> by_cases h2 : b=j <;> by_cases h3 : i=j <;> by_cases h4 : a=b
  all_goals simp_all only [and_self,ite_true,ite_false,and_false,false_and,star_one,star_zero,
    mul_one,mul_zero,add_zero,zero_add,sub_zero,zero_sub]
  all_goals field_simp
  all_goals ring

/-- The complement Choi entry is d R0, not R0. -/
theorem radialChoiR0_scaled_entry (d : ℕ) (i a j b : Fin d) :
    (d:ℂ)*radialChoiR0 d (i,a) (j,b)=
      ((d:ℂ)*(if i=j ∧ a=b then 1 else 0)-(if a=i ∧ b=j then 1 else 0))/(d+1:ℂ) := by
  have hd : 0<d := Nat.zero_lt_of_lt i.isLt
  have hd0 : (d:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hd
  simp only [radialChoiR0,radialChoiPhi,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,unitaryBellProjector_entry,Fintype.card_fin,Matrix.one_apply,Prod.mk.injEq]
  by_cases h1 : a=i <;> by_cases h2 : b=j <;> by_cases h3 : i=j <;> by_cases h4 : a=b
  all_goals simp_all only [and_self,ite_true,ite_false,and_false,false_and,star_one,star_zero,
    mul_one,mul_zero,sub_zero,zero_sub]
  all_goals field_simp
  all_goals ring

/-- Matrix units extract exactly the transposed input coordinate in the readout Choi convention. -/
theorem matrix_trace_mul_single_one {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (i j : I) : Matrix.trace (A*Matrix.single i j 1)=A j i := by
  simp [Matrix.trace_mul_single]

/-- A genuine full-record success twirl supplies the actual local Choi entry. -/
theorem localReadoutChoi_success {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (hd : 0<d) (μ : Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (hs : ∀ (A : Matrix (Fin d) (Fin d) ℂ) a b,
      (d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*
        Matrix.trace (recordedProjector d (record ω)*A)∂μ)=
        (A a b+if a=b then Matrix.trace A else 0)/(d+1:ℂ)) (i a j b : Fin d) :
    (d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*recordedProjector d (record ω) j i∂μ)=
      radialChoiA0 d (i,a) (j,b) := by
  have h := hs (Matrix.single i j 1) a b
  simp only [matrix_trace_mul_single_one] at h
  have ht : Matrix.trace (Matrix.single i j (1:ℂ))=if i=j then 1 else 0 := by
    by_cases hij : i=j <;> simp [hij]
  rw [h,radialChoiA0_entry d hd,ht]
  by_cases hab : a=b <;> by_cases hij : i=j <;>
    simp [Matrix.single,hab,hij,eq_comm,and_comm]

/-- A genuine full-record complement twirl supplies the factor d R0. -/
theorem localReadoutChoi_complement {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (μ : Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (hf : ∀ (A : Matrix (Fin d) (Fin d) ℂ) a b,
      (d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*
        Matrix.trace ((1-recordedProjector d (record ω))*A)∂μ)=
        (((d:ℂ)*Matrix.trace A)*(if a=b then 1 else 0)-A a b)/(d+1:ℂ)) (i a j b : Fin d) :
    (d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*
      (1-recordedProjector d (record ω)) j i∂μ)=(d:ℂ)*radialChoiR0 d (i,a) (j,b) := by
  have h := hf (Matrix.single i j 1) a b
  simp only [matrix_trace_mul_single_one] at h
  have ht : Matrix.trace (Matrix.single i j (1:ℂ))=if i=j then 1 else 0 := by
    by_cases hij : i=j <;> simp [hij]
  rw [h,radialChoiR0_scaled_entry,ht]
  by_cases hab : a=b <;> by_cases hij : i=j <;>
    simp [Matrix.single,hab,hij,eq_comm,and_comm]

/-- Both local factors use the actual full Haar basis/outcome reference law. -/
theorem haarBasisRecords_choi_entries (d : ℕ) [NeZero d] (i a j b : Fin d) :
    ((d:ℂ)*(∫ ω,recordedProjector d ω a b*recordedProjector d ω j i∂haarBasisRecords d)=
      radialChoiA0 d (i,a) (j,b)) ∧
    ((d:ℂ)*(∫ ω,recordedProjector d ω a b*(1-recordedProjector d ω) j i∂haarBasisRecords d)=
      (d:ℂ)*radialChoiR0 d (i,a) (j,b)) :=
  ⟨localReadoutChoi_success d (Nat.pos_of_ne_zero (NeZero.ne d)) (haarBasisRecords d) id
      (haarBasisRecords_success d) i a j b,
    localReadoutChoi_complement d (haarBasisRecords d) id (haarBasisRecords_complement d) i a j b⟩

/-- The finite three-Pauli-basis complete records have exactly the same two Choi factors at d=2. -/
theorem pauliBasisRecords_choi_entries (i a j b : Fin 2) :
    ((2:ℂ)*(∫ ω,pauliRecordedProjector ω a b*pauliRecordedProjector ω j i∂pauliBasisRecords)=
      radialChoiA0 2 (i,a) (j,b)) ∧
    ((2:ℂ)*(∫ ω,pauliRecordedProjector ω a b*(1-pauliRecordedProjector ω) j i∂pauliBasisRecords)=
      (2:ℂ)*radialChoiR0 2 (i,a) (j,b)) := by
  constructor
  · apply localReadoutChoi_success 2 (by norm_num) pauliBasisRecords pauliFullRecord
    intro A a b
    simpa only [pauliRecordedProjector,Nat.cast_ofNat,show (2:ℂ)+1=3 by norm_num] using pauliBasisRecords_success A a b
  · apply localReadoutChoi_complement 2 pauliBasisRecords pauliFullRecord
    intro A a b
    have h := pauliBasisRecords_complement A a b
    by_cases hab : a=b <;> simpa [pauliRecordedProjector,hab,show (2:ℂ)+1=3 by norm_num] using h

end CertificationGaussian
