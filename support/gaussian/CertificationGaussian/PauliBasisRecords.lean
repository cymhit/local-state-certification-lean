import CertificationGaussian.HaarGraphKappa

noncomputable section
open MeasureTheory Metric Set Matrix
open scoped BigOperators ComplexConjugate
namespace CertificationGaussian

/-- The positive real normalization used by the X and Y Pauli bases. -/
def pauliAmplitude : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

@[simp] theorem pauliAmplitude_star : star pauliAmplitude=pauliAmplitude := by
  simp [pauliAmplitude]

@[simp] theorem pauliAmplitude_conj : conj pauliAmplitude=pauliAmplitude := Complex.conj_ofReal _

@[simp] theorem pauliAmplitude_sq : pauliAmplitude^2=(1/2:ℂ) := by
  unfold pauliAmplitude
  rw [← Complex.ofReal_pow,inv_pow,Real.sq_sqrt (by norm_num)]
  norm_num

/-- The actual Z, X and Y orthonormal bases, with both outcomes retained. -/
def pauliBasisMatrix (b : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![1,!![pauliAmplitude,pauliAmplitude;pauliAmplitude,-pauliAmplitude],
    !![pauliAmplitude,pauliAmplitude;Complex.I*pauliAmplitude,-Complex.I*pauliAmplitude]] b

theorem pauliBasisMatrix_unitary (b : Fin 3) :
    pauliBasisMatrix b ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.mem_unitaryGroup_iff']
  fin_cases b
  all_goals ext i j; fin_cases i <;> fin_cases j
  all_goals norm_num [pauliBasisMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fin.sum_univ_two,star_mul,star_neg,show star Complex.I = -Complex.I from Complex.conj_I]
  all_goals ring_nf
  all_goals norm_num [pauliAmplitude_conj]

def pauliBasisUnitary (b : Fin 3) : ComplexUnitary (Fin 2) :=
  ⟨pauliBasisMatrix b,pauliBasisMatrix_unitary b⟩

/-- Finite reference records contain the Pauli basis label and the outcome label. -/
abbrev PauliRecord := Fin 3 × Fin 2

def pauliBasisRecords : Measure PauliRecord := (uniformFiniteOutcome 3).prod (uniformFiniteOutcome 2)

instance pauliBasisRecords_probability : IsProbabilityMeasure pauliBasisRecords := by
  unfold pauliBasisRecords
  infer_instance

def pauliFullRecord (ω : PauliRecord) : ComplexUnitary (Fin 2) × Fin 2 :=
  (pauliBasisUnitary ω.1,ω.2)

def pauliRecordedUnitVector (ω : PauliRecord) : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 :=
  haarRecordedUnitVector 2 (pauliFullRecord ω)

@[fun_prop] theorem pauliRecordedUnitVector_continuous : Continuous pauliRecordedUnitVector :=
  continuous_of_discreteTopology

theorem pauliRecordedUnitVector_apply (ω : PauliRecord) (i : Fin 2) :
    (pauliRecordedUnitVector ω).val i=pauliBasisMatrix ω.1 i ω.2 :=
  haarRecordedUnitVector_apply 2 (pauliFullRecord ω) i

/-- This is the projector of the actual Pauli basis column, not a surrogate outcome. -/
def pauliRecordedProjector (ω : PauliRecord) : Matrix (Fin 2) (Fin 2) ℂ :=
  recordedProjector 2 (pauliFullRecord ω)

theorem pauliRecordedProjector_apply (ω : PauliRecord) (i j : Fin 2) :
    pauliRecordedProjector ω i j =
      (pauliRecordedUnitVector ω).val i*star ((pauliRecordedUnitVector ω).val j) :=
  haarRecordedUnitVector_projector 2 (pauliFullRecord ω) i j

/-- The reference law is exactly uniform on all six complete basis/outcome records. -/
theorem pauliBasisRecords_integral (f : PauliRecord → ℝ) :
    (∫ ω, f ω ∂pauliBasisRecords)=(1/6:ℝ)*∑ b : Fin 3,∑ j : Fin 2,f (b,j) := by
  have hi : Integrable f pauliBasisRecords :=
    (show Continuous f from continuous_of_discreteTopology).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [pauliBasisRecords,integral_prod _ hi]
  simp_rw [uniformFiniteOutcome_real_integral]
  norm_num only [Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  ring

/-- The three actual Pauli bases are mutually unbiased, with same-basis orthogonality. -/
theorem pauli_record_overlap_sq (a b : PauliRecord) :
    recordOverlap pauliRecordedUnitVector a b^2 =
      if a.1=b.1 then (if a.2=b.2 then 1 else 0) else (1/2:ℝ) := by
  obtain ⟨a,j⟩ := a
  obtain ⟨b,k⟩ := b
  have hs : ((Real.sqrt (2:ℝ))⁻¹)^2=(1/2:ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hs4 : ((Real.sqrt (2:ℝ))⁻¹)^4=(1/4:ℝ) := by
    calc
      _ = (((Real.sqrt (2:ℝ))⁻¹)^2)^2 := by ring
      _ = 1/4 := by rw [hs]; norm_num
  have hr4 : Real.sqrt (2:ℝ)^4=4 := by
    calc
      _ = (Real.sqrt (2:ℝ)^2)^2 := by ring
      _ = 4 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  fin_cases a <;> fin_cases b <;> fin_cases j <;> fin_cases k
  all_goals norm_num [recordOverlap,Complex.sq_norm,PiLp.inner_apply,RCLike.inner_apply',
    pauliRecordedUnitVector_apply,pauliBasisMatrix,Fin.sum_univ_two,Complex.normSq_apply,
    pauliAmplitude,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.conj_re,Complex.conj_im]
  all_goals ring_nf
  all_goals norm_num [← inv_pow,hs,hs4,hr4]

/-- Exact absolute overlaps of the six actual Pauli records. -/
theorem pauli_record_overlap (a b : PauliRecord) :
    recordOverlap pauliRecordedUnitVector a b =
      if a.1=b.1 then (if a.2=b.2 then 1 else 0) else (Real.sqrt 2)⁻¹ := by
  apply (sq_eq_sq₀ (recordOverlap_nonneg _ _ _) (by split_ifs <;> positivity)).mp
  rw [pauli_record_overlap_sq]
  split_ifs <;> norm_num [inv_pow,Real.sq_sqrt]

theorem pauli_record_overlap_sixth (a b : PauliRecord) :
    recordOverlap pauliRecordedUnitVector a b^6 =
      if a.1=b.1 then (if a.2=b.2 then 1 else 0) else (1/8:ℝ) := by
  rw [show recordOverlap pauliRecordedUnitVector a b^6 =
    (recordOverlap pauliRecordedUnitVector a b^2)^3 by ring,pauli_record_overlap_sq]
  split_ifs <;> norm_num

/-- Every one of the actual six records has sixth overlap moment 1/4. -/
theorem pauliBasisRecords_overlap_sixth (a : PauliRecord) :
    (∫ b, recordOverlap pauliRecordedUnitVector a b^6 ∂pauliBasisRecords)=(1/4:ℝ) := by
  rw [pauliBasisRecords_integral]
  simp_rw [pauli_record_overlap_sixth]
  obtain ⟨a,j⟩ := a
  fin_cases a <;> fin_cases j <;> norm_num [Fin.sum_univ_succ]

end CertificationGaussian
