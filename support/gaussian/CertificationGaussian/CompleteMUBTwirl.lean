import CertificationGaussian.CompleteMUBRecords
import CertificationGaussian.RankOneWickContraction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate
namespace CertificationGaussian
variable {d : ℕ} [NeZero d] (B : CompleteMUB d)

omit [NeZero d] in
theorem completeMUB_projector_sum (b : Fin (d+1)) :
    ∑ j : Fin d,completeMUBProjector B (b,j)=1 :=
  sum_columnProjector (Fin d) (B.basis b)

omit [NeZero d] in
theorem completeMUB_projector_trace (a : CompleteMUBRecord d) :
    Matrix.trace (completeMUBProjector B a)=1 :=
  unitary_columnProjector_trace (Fin d) (B.basis a.1) a.2

theorem completeMUB_projector_eq_rankOne (a : CompleteMUBRecord d) :
    completeMUBProjector B a=
      vectorRankOne (completeMUBUnitVector B a).val (completeMUBUnitVector B a).val := by
  ext i j
  exact completeMUBProjector_apply B a i j

/-- Trace pairings are derived from the actual recorded projectors. -/
theorem completeMUB_projector_pairing (a b : CompleteMUBRecord d) :
    Matrix.trace (completeMUBProjector B a*completeMUBProjector B b)=
      if a.1=b.1 then (if a.2=b.2 then 1 else 0) else (d:ℂ)⁻¹ := by
  rw [completeMUB_projector_eq_rankOne,completeMUB_projector_eq_rankOne,
    vectorRankOne_mul,Matrix.trace_smul,vectorRankOne_trace]
  simp only [smul_eq_mul]
  have hconj : inner ℂ (completeMUBUnitVector B b).val (completeMUBUnitVector B a).val=
      conj (inner ℂ (completeMUBUnitVector B a).val (completeMUBUnitVector B b).val) :=
    (inner_conj_symm _ _).symm
  rw [hconj,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  have he := congrArg (fun t : ℝ => (t:ℂ)) (completeMUB_overlap_sq B a b)
  split_ifs at he ⊢ <;> simpa [recordOverlap] using he

/-- The unnormalized finite basis-dephasing sum; its linearity holds for arbitrary complex matrices. -/
def completeMUBFrameMap : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun A := ∑ b : Fin (d+1),∑ j : Fin d,
    Matrix.trace (completeMUBProjector B (b,j)*A) • completeMUBProjector B (b,j)
  map_add' A C := by
    simp only [Matrix.mul_add,Matrix.trace_add,add_smul,Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Matrix.mul_smul,Matrix.trace_smul,smul_smul,Finset.smul_sum,smul_eq_mul]
    rfl

/-- First moment of the same complete reference records. -/
theorem completeMUBRecords_projector_mean (i j : Fin d) :
    (d:ℂ)*(∫ ω,completeMUBProjector B ω i j∂completeMUBRecords d)=
      (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  rw [completeMUBRecords_complex_integral]
  have hs (b : Fin (d+1)) : (∑ k : Fin d,completeMUBProjector B (b,k) i j)=
      (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) (completeMUB_projector_sum B b)
    simpa only [Matrix.sum_apply] using h
  simp_rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have hd : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
  have hd1 : (d+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero d
  field_simp

/-- The finite frame sum has the intended action on each actual recorded projector. -/
theorem completeMUBFrameMap_projector (a : CompleteMUBRecord d) :
    completeMUBFrameMap B (completeMUBProjector B a)=completeMUBProjector B a+1 := by
  have hb (b : Fin (d+1)) :
      (∑ j : Fin d, Matrix.trace (completeMUBProjector B (b,j)*completeMUBProjector B a) •
        completeMUBProjector B (b,j)) =
        if b=a.1 then completeMUBProjector B a else (d:ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    simp_rw [completeMUB_projector_pairing]
    by_cases h : b=a.1
    · subst b
      simp only [ite_true]
      simp
    · simp only [h,ite_false]
      rw [← Finset.smul_sum,completeMUB_projector_sum]
  change (∑ b : Fin (d+1),∑ j : Fin d,_)=_
  simp_rw [hb]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a.1)]
  have he : (∑ b ∈ Finset.univ.erase a.1,
      if b=a.1 then completeMUBProjector B a else (d:ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ))=
      (d:ℂ) • ((d:ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    calc
      _=∑ b ∈ Finset.univ.erase a.1,(d:ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [ite_eq_right (Finset.ne_of_mem_erase hb)]
      _=_ := by
        simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ a.1),
          Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel]
        rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [he,ite_eq_left rfl,smul_smul]
  have hd : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
  rw [mul_inv_cancel₀ hd,one_smul,add_comm]

omit [NeZero d] in
theorem completeMUBFrameMap_one :
    completeMUBFrameMap B (1 : Matrix (Fin d) (Fin d) ℂ)=
      (d+1:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  change (∑ b : Fin (d+1),∑ j : Fin d,_)=_
  simp only [Matrix.mul_one,completeMUB_projector_trace,one_smul,completeMUB_projector_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [Nat.cast_add,Nat.cast_one]


/-- One trace direction and the differences within each actual MUB basis. -/
abbrev CompleteMUBSpanIndex (d : ℕ) [NeZero d] :=
  Option (Fin (d+1) × {j : Fin d // j ≠ 0})

def completeMUBSpanVector : CompleteMUBSpanIndex d → Matrix (Fin d) (Fin d) ℂ
  | none => 1
  | some (b,j) => completeMUBProjector B (b,j.val)-completeMUBProjector B (b,0)

theorem completeMUBSpanVector_trace (k : CompleteMUBSpanIndex d) :
    Matrix.trace (completeMUBSpanVector B k)=if k=none then (d:ℂ) else 0 := by
  cases k with
  | none => simp [completeMUBSpanVector,Matrix.trace_one]
  | some k => simp [completeMUBSpanVector,Matrix.trace_sub,completeMUB_projector_trace]

theorem completeMUBSpanVector_pairing
    (a : Fin (d+1) × {j : Fin d // j≠0}) (k : CompleteMUBSpanIndex d) :
    Matrix.trace (completeMUBProjector B (a.1,a.2.val)*completeMUBSpanVector B k)=
      if k=none then 1 else if k=some a then 1 else 0 := by
  cases k with
  | none => simp [completeMUBSpanVector,completeMUB_projector_trace]
  | some k =>
    rcases a with ⟨a,i⟩
    rcases k with ⟨b,j⟩
    simp only [completeMUBSpanVector,Matrix.mul_sub,Matrix.trace_sub,
      completeMUB_projector_pairing,Option.some_ne_none,ite_false,Option.some.injEq]
    by_cases hab : a=b
    · subst b
      by_cases hij : i=j
      · subst j
        simp [i.property]
      · have hv : i.val≠j.val := fun h => hij (Subtype.ext h)
        simp [hv,i.property,Ne.symm hij]
    · simp [hab,Ne.symm hab]

theorem completeMUBSpanVector_linearIndependent :
    LinearIndependent ℂ (completeMUBSpanVector B) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have ht := congrArg Matrix.trace hc
  simp only [Matrix.trace_sum,Matrix.trace_smul,completeMUBSpanVector_trace,
    smul_eq_mul,Matrix.trace_zero] at ht
  have hn : c none=0 := by
    have ht' : c none*(d:ℂ)=0 := by simpa using ht
    exact (mul_eq_zero.mp ht').resolve_right (by exact_mod_cast NeZero.ne d)
  intro k
  cases k with
  | none => exact hn
  | some a =>
    have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ =>
      Matrix.trace (completeMUBProjector B (a.1,a.2.val)*M)) hc
    simp only [Matrix.mul_sum,Matrix.trace_sum,Matrix.mul_smul,Matrix.trace_smul,
      completeMUBSpanVector_pairing,smul_eq_mul,Matrix.mul_zero,Matrix.trace_zero] at he
    simpa [hn] using he



theorem completeMUBSpanIndex_card :
    Fintype.card (CompleteMUBSpanIndex d)=Module.finrank ℂ (Matrix (Fin d) (Fin d) ℂ) := by
  have hd : 1≤d := NeZero.pos d
  simp only [CompleteMUBSpanIndex,Fintype.card_option,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_unique]
  simp only [Module.finrank_matrix,Module.finrank_self,Fintype.card_fin,mul_one]
  have hh : d-1+1=d := Nat.sub_add_cancel hd
  nlinarith

def completeMUBTraceMap : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun A := A+Matrix.trace A • 1
  map_add' A C := by simp only [Matrix.trace_add,add_smul]; abel
  map_smul' c A := by simp only [Matrix.trace_smul,smul_add,smul_smul,smul_eq_mul]; rfl

/-- Completeness is proved by a concrete matrix-space basis, not postulated as a design identity. -/
theorem completeMUBFrameMap_eq_traceMap :
    completeMUBFrameMap B=completeMUBTraceMap (d:=d) := by
  let b := basisOfLinearIndependentOfCardEqFinrank' (completeMUBSpanVector B)
    (completeMUBSpanVector_linearIndependent B) (completeMUBSpanIndex_card (d:=d))
  apply b.ext
  intro k
  simp only [b,coe_basisOfLinearIndependentOfCardEqFinrank']
  change completeMUBFrameMap B (completeMUBSpanVector B k)=
    completeMUBTraceMap (completeMUBSpanVector B k)
  cases k with
  | none =>
    change completeMUBFrameMap B 1=1+Matrix.trace (1:Matrix (Fin d) (Fin d) ℂ) • 1
    rw [completeMUBFrameMap_one,Matrix.trace_one]
    simp only [Fintype.card_fin,add_smul,one_smul]
    abel
  | some k =>
    change completeMUBFrameMap B (completeMUBProjector B (k.1,k.2.val)-completeMUBProjector B (k.1,0))=_
    rw [map_sub,completeMUBFrameMap_projector,completeMUBFrameMap_projector]
    change _=completeMUBSpanVector B (some k)+Matrix.trace (completeMUBSpanVector B (some k)) • 1
    rw [completeMUBSpanVector_trace]
    simp only [Option.some_ne_none,ite_false,zero_smul,add_zero,completeMUBSpanVector]
    abel

theorem completeMUBFrameMap_apply (A : Matrix (Fin d) (Fin d) ℂ) :
    completeMUBFrameMap B A=A+Matrix.trace A • 1 := by
  rw [completeMUBFrameMap_eq_traceMap]
  rfl



/-- Success twirl under the actual uniform basis/outcome reference measure, for every complex A. -/
theorem completeMUBRecords_success (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (d:ℂ)*(∫ ω,completeMUBProjector B ω i j*Matrix.trace (completeMUBProjector B ω*A)
      ∂completeMUBRecords d)=(A i j+if i=j then Matrix.trace A else 0)/(d+1:ℂ) := by
  rw [completeMUBRecords_complex_integral]
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) (completeMUBFrameMap_apply B A)
  have hs : (∑ b : Fin (d+1),∑ k : Fin d,
      completeMUBProjector B (b,k) i j*Matrix.trace (completeMUBProjector B (b,k)*A))=
      A i j+if i=j then Matrix.trace A else 0 := by
    simpa [completeMUBFrameMap,Matrix.sum_apply,Matrix.smul_apply,Matrix.one_apply,mul_comm] using he
  rw [hs]
  have hd : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
  have hq : (d+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero d
  field_simp

/-- The complement twirl retains the same actual record and its actual complementary effect. -/
theorem completeMUBRecords_complement (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (d:ℂ)*(∫ ω,completeMUBProjector B ω i j*Matrix.trace ((1-completeMUBProjector B ω)*A)
      ∂completeMUBRecords d)=
      (((d:ℂ)*Matrix.trace A)*(if i=j then 1 else 0)-A i j)/(d+1:ℂ) := by
  have hi (f : CompleteMUBRecord d → ℂ) : Integrable f (completeMUBRecords d) :=
    (show Continuous f from continuous_of_discreteTopology).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [Matrix.sub_mul,one_mul,Matrix.trace_sub,mul_sub]
  rw [integral_sub (hi _) (hi _),mul_sub,integral_mul_const,← mul_assoc,
    completeMUBRecords_projector_mean,completeMUBRecords_success]
  have hq : (d+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero d
  by_cases hij : i=j <;> simp [hij,Matrix.one_apply]
  all_goals field_simp <;> ring


end CertificationGaussian
