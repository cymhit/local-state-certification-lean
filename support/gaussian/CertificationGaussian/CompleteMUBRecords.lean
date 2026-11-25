import CertificationGaussian.PauliGraphKappa
import CertificationGaussian.PauliTwirl

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate
namespace CertificationGaussian

/-- Supplied complete MUBs are genuine unitary bases. The only extra input is mutual unbiasedness;
neither a design identity, a moment value nor a graph-contraction estimate is assumed. -/
structure CompleteMUB (d : ℕ) where
  basis : Fin (d+1) → ComplexUnitary (Fin d)
  unbiased : ∀ b c : Fin (d+1), b≠c → ∀ i j : Fin d,
    ‖((basis b).valᴴ*(basis c).val) i j‖^2=(d:ℝ)⁻¹

abbrev CompleteMUBRecord (d : ℕ) := Fin (d+1) × Fin d

/-- Both the basis label and the observed column remain in the reference record. -/
def completeMUBRecords (d : ℕ) : Measure (CompleteMUBRecord d) :=
  (uniformFiniteOutcome (d+1)).prod (uniformFiniteOutcome d)

instance completeMUBRecords_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (completeMUBRecords d) := by
  unfold completeMUBRecords
  infer_instance

def completeMUBFullRecord {d : ℕ} (B : CompleteMUB d) (ω : CompleteMUBRecord d) :
    ComplexUnitary (Fin d) × Fin d := (B.basis ω.1,ω.2)

def completeMUBProjector {d : ℕ} (B : CompleteMUB d) (ω : CompleteMUBRecord d) :
    Matrix (Fin d) (Fin d) ℂ := recordedProjector d (completeMUBFullRecord B ω)

def completeMUBUnitVector {d : ℕ} [NeZero d] (B : CompleteMUB d) (ω : CompleteMUBRecord d) :
    sphere (0 : EuclideanSpace ℂ (Fin d)) 1 :=
  haarRecordedUnitVector d (completeMUBFullRecord B ω)

@[fun_prop] theorem completeMUBUnitVector_continuous {d : ℕ} [NeZero d] (B : CompleteMUB d) :
    Continuous (completeMUBUnitVector B) := continuous_of_discreteTopology

theorem completeMUBUnitVector_apply {d : ℕ} [NeZero d] (B : CompleteMUB d)
    (ω : CompleteMUBRecord d) (i : Fin d) :
    (completeMUBUnitVector B ω).val i=(B.basis ω.1).val i ω.2 :=
  haarRecordedUnitVector_apply d _ i

theorem completeMUBProjector_apply {d : ℕ} [NeZero d] (B : CompleteMUB d)
    (ω : CompleteMUBRecord d) (i j : Fin d) :
    completeMUBProjector B ω i j=
      (completeMUBUnitVector B ω).val i*star ((completeMUBUnitVector B ω).val j) :=
  haarRecordedUnitVector_projector d _ i j

theorem completeMUB_column_inner {d : ℕ} [NeZero d] (B : CompleteMUB d)
    (a b : CompleteMUBRecord d) :
    inner ℂ (completeMUBUnitVector B a).val (completeMUBUnitVector B b).val=
      ((B.basis a.1).valᴴ*(B.basis b.1).val) a.2 b.2 := by
  simp only [PiLp.inner_apply,RCLike.inner_apply',completeMUBUnitVector_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.star_def]

/-- Same-basis orthogonality and cross-basis unbiasedness refer to the actual recorded vectors. -/
theorem completeMUB_overlap_sq {d : ℕ} [NeZero d] (B : CompleteMUB d)
    (a b : CompleteMUBRecord d) :
    recordOverlap (completeMUBUnitVector B) a b^2=
      if a.1=b.1 then (if a.2=b.2 then 1 else 0) else (d:ℝ)⁻¹ := by
  unfold recordOverlap
  rw [completeMUB_column_inner]
  by_cases h : a.1=b.1
  · have he : (B.basis b.1).valᴴ*(B.basis b.1).val=1 := (B.basis b.1).property.1
    rw [h,he]
    by_cases hi : a.2=b.2 <;> simp [hi,Matrix.one_apply]
  · simpa only [h,ite_false] using B.unbiased a.1 b.1 h a.2 b.2

theorem completeMUB_overlap {d : ℕ} [NeZero d] (B : CompleteMUB d)
    (a b : CompleteMUBRecord d) :
    recordOverlap (completeMUBUnitVector B) a b=
      if a.1=b.1 then (if a.2=b.2 then 1 else 0) else (Real.sqrt d)⁻¹ := by
  apply (sq_eq_sq₀ (recordOverlap_nonneg _ _ _) (by split_ifs <;> positivity)).mp
  rw [completeMUB_overlap_sq]
  split_ifs <;> simp [inv_pow,Real.sq_sqrt]

theorem completeMUB_overlap_sixth {d : ℕ} [NeZero d] (B : CompleteMUB d)
    (a b : CompleteMUBRecord d) :
    recordOverlap (completeMUBUnitVector B) a b^6=
      if a.1=b.1 then (if a.2=b.2 then 1 else 0) else ((d:ℝ)⁻¹)^3 := by
  rw [show recordOverlap (completeMUBUnitVector B) a b^6=
    (recordOverlap (completeMUBUnitVector B) a b^2)^3 by ring,completeMUB_overlap_sq]
  split_ifs <;> norm_num

theorem completeMUBRecords_integral (d : ℕ) [NeZero d] (f : CompleteMUBRecord d → ℝ) :
    (∫ ω,f ω∂completeMUBRecords d)=((d+1:ℝ)*(d:ℝ))⁻¹*∑ b,∑ j,f (b,j) := by
  have hi : Integrable f (completeMUBRecords d) :=
    finite_readout_integrable _ _
  rw [completeMUBRecords,integral_prod _ hi]
  simp_rw [uniformFiniteOutcome_real_integral]
  rw [← Finset.mul_sum]
  push_cast
  rw [_root_.mul_inv_rev]
  ring

theorem completeMUBRecords_complex_integral (d : ℕ) [NeZero d] (f : CompleteMUBRecord d → ℂ) :
    (∫ ω,f ω∂completeMUBRecords d)=((d+1:ℂ)*(d:ℂ))⁻¹*∑ b,∑ j,f (b,j) := by
  have hi : Integrable f (completeMUBRecords d) :=
    (show Continuous f from continuous_of_discreteTopology).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [completeMUBRecords,integral_prod _ hi]
  simp_rw [uniformFiniteOutcome_integral]
  rw [← Finset.mul_sum]
  push_cast
  rw [_root_.mul_inv_rev]
  ring

/-- The exact sixth moment holds for every record of this ensemble, not for arbitrary vectors. -/
theorem completeMUBRecords_overlap_sixth {d : ℕ} [NeZero d] (B : CompleteMUB d)
    (a : CompleteMUBRecord d) :
    (∫ b,recordOverlap (completeMUBUnitVector B) a b^6∂completeMUBRecords d)=((d:ℝ)⁻¹)^2 := by
  rw [completeMUBRecords_integral]
  simp_rw [completeMUB_overlap_sixth]
  have hi (b : Fin (d+1)) :
      (∑ j : Fin d,if a.1=b then (if a.2=j then (1:ℝ) else 0) else ((d:ℝ)⁻¹)^3)=
        if b=a.1 then 1 else (d:ℝ)*((d:ℝ)⁻¹)^3 := by
    by_cases h : b=a.1 <;> simp [h,eq_comm]
  simp_rw [hi]
  have hsum : (∑ b : Fin (d+1),if b=a.1 then (1:ℝ) else (d:ℝ)*((d:ℝ)⁻¹)^3)=
      1+(d:ℝ)*((d:ℝ)*((d:ℝ)⁻¹)^3) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a.1)]
    have he : (∑ b ∈ Finset.univ.erase a.1,
        if b=a.1 then (1:ℝ) else (d:ℝ)*((d:ℝ)⁻¹)^3)=
        (d:ℝ)*((d:ℝ)*((d:ℝ)⁻¹)^3) := by
      calc
        _=∑ b ∈ Finset.univ.erase a.1,(d:ℝ)*((d:ℝ)⁻¹)^3 := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [ite_eq_right (Finset.ne_of_mem_erase hb)]
        _=_ := by simp
    rw [he,ite_eq_left rfl]
    ring
  rw [hsum]
  have hd : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
  have hd1 : (d+1:ℝ)≠0 := by positivity
  field_simp

end CertificationGaussian
