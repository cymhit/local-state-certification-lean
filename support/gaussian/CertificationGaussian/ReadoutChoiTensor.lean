import CertificationGaussian.ReadoutChoiLocal

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
namespace CertificationGaussian

/-- The actual readout Choi matrix: input indices are transposed, and the reference-law factor is D. -/
def readoutChoiMatrix {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℝ) (P H : Ω → Matrix I I ℂ) : Matrix (I×I) (I×I) ℂ :=
  fun p q => (D:ℂ)*(∫ ω,P ω p.2 q.2*H ω q.1 p.1∂μ)

/-- True product-record factorization gives d^|J| times the same original tensor Choi matrix. -/
theorem productReadoutChoi_eq {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (hentry : ∀ i a j b : Fin d,
      ((d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*recordedProjector d (record ω) j i∂μ)=
        radialChoiA0 d (i,a) (j,b)) ∧
      ((d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*(1-recordedProjector d (record ω)) j i∂μ)=
        (d:ℂ)*radialChoiR0 d (i,a) (j,b))) (J : Finset S) :
    readoutChoiMatrix (Measure.pi (fun _ : S => μ)) ((d:ℝ)^(Fintype.card S))
      (productRecordedProjector d record) (productReadoutFactor d record J)=
      (d:ℂ)^J.card • radialChoiTensor d J := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [readoutChoiMatrix,productRecordedProjector,productReadoutFactor,wickTensorMatrix,
    ← Finset.prod_mul_distrib,Complex.ofReal_pow,Complex.ofReal_natCast]
  rw [integral_fintype_prod_eq_prod (fun (s : S) (ω : Ω) =>
    recordedProjector d (record ω) (a s) (b s)*
      localReadoutFactor d (decide (s∈J)) (record ω) (j s) (i s))]
  calc
    _ = ∏ s : S,(d:ℂ)*(∫ ω,recordedProjector d (record ω) (a s) (b s)*
        localReadoutFactor d (decide (s∈J)) (record ω) (j s) (i s)∂μ) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ]
    _ = ∏ s : S,(if s∈J then (d:ℂ) else 1)*
        (if s∈J then radialChoiR0 d else radialChoiA0 d) (i s,a s) (j s,b s) := by
      apply Finset.prod_congr rfl
      intro s _
      by_cases hs : s∈J
      · simpa [hs,localReadoutFactor] using
          (hentry (i s) (a s) (j s) (b s)).2
      · simpa [hs,localReadoutFactor] using
          (hentry (i s) (a s) (j s) (b s)).1
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_ite,Finset.filter_mem_eq_inter,Finset.univ_inter,
        Finset.prod_const,one_pow,mul_one,Matrix.smul_apply,smul_eq_mul,
        radialChoiTensor,pairedTensorMatrix]

section Continuous
variable {Ω I T : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [Fintype T]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Additivity is justified by the actual compact-record integrability. -/
theorem readoutChoiMatrix_sum (D : ℝ) (P : Ω → Matrix I I ℂ) (H : T → Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : ∀ t,Continuous (H t)) :
    readoutChoiMatrix μ D P (fun ω => ∑ t,H t ω)=∑ t,readoutChoiMatrix μ D P (H t) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [readoutChoiMatrix,Matrix.sum_apply,Finset.mul_sum]
  rw [integral_finsetSum _ (fun t _ =>
    (show Continuous (fun ω => P ω a b*H t ω j i) from
      ((continuous_apply b).comp ((continuous_apply a).comp hP)).mul
        ((continuous_apply i).comp ((continuous_apply j).comp (hH t)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)),Finset.mul_sum]

omit [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Fintype T] [IsProbabilityMeasure μ] in
/-- Actual complex scalar linearity of the readout Choi matrix. -/
theorem readoutChoiMatrix_smul (D : ℝ) (P H : Ω → Matrix I I ℂ) (c : ℂ) :
    readoutChoiMatrix μ D P (fun ω => c • H ω)=c • readoutChoiMatrix μ D P H := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [readoutChoiMatrix,Matrix.smul_apply,smul_eq_mul]
  simp_rw [mul_left_comm (P _ _ _) c]
  rw [integral_const_mul]
  ring
end Continuous

/-- The true complete-record Choi matrix of the original cardinality kernel equals the original radial tensor formula. -/
theorem cardinalityReadoutChoi_eq {S Ω : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω] (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (hentry : ∀ i a j b : Fin d,
      ((d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*recordedProjector d (record ω) j i∂μ)=
        radialChoiA0 d (i,a) (j,b)) ∧
      ((d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*(1-recordedProjector d (record ω)) j i∂μ)=
        (d:ℂ)*radialChoiR0 d (i,a) (j,b))) (r : ℕ) (lam : ℕ → ℝ) :
    readoutChoiMatrix (Measure.pi (fun _ : S => μ)) ((d:ℝ)^(Fintype.card S))
      (productRecordedProjector d record) (cardinalityReadoutKernel d record r lam)=
      radialChoiCombination d r lam := by
  have hP := productRecordedProjector_continuous (S:=S) d record hr
  have hH (J : Finset S) : Continuous (productReadoutFactor d record J) :=
    productReadoutFactor_continuous d record hr J
  have he : cardinalityReadoutKernel (S:=S) d record r lam=
      (fun ω => ∑ j : Fin (r+1),(lam j.val:ℂ) •
        ∑ J : {A : Finset S // A.card=j.val},productReadoutFactor d record J.val ω) := by
    funext ω
    exact cardinalityReadoutKernel_formula d record r lam ω
  have hsum (j : Fin (r+1)) : Continuous (fun ω : S → Ω => (lam j.val:ℂ) •
      ∑ J : {A : Finset S // A.card=j.val},productReadoutFactor d record J.val ω) :=
    (continuous_const (y := (lam j.val:ℂ))).smul
      (continuous_finsetSum Finset.univ (fun (J : {A : Finset S // A.card=j.val}) _ => hH J.val))
  rw [he,readoutChoiMatrix_sum _ _ _ _ hP hsum]
  simp_rw [readoutChoiMatrix_smul]
  unfold radialChoiCombination
  apply Finset.sum_congr rfl
  intro j _
  rw [readoutChoiMatrix_sum _ _ _ _ hP (fun (J : {A : Finset S // A.card=j.val}) => hH J.val)]
  simp_rw [productReadoutChoi_eq d μ record hentry]
  have hc (J : {A : Finset S // A.card=j.val}) : J.val.card=j.val := J.property
  simp only [hc,← Finset.smul_sum,smul_smul]
  congr 1
  ring

/-- Actual full-Haar records give the original cardinality Choi matrix, with all local premises discharged. -/
theorem cardinalityHaar_choi {S : Type*} [Fintype S] [DecidableEq S]
    (d r : ℕ) [NeZero d] (lam : ℕ → ℝ) :
    readoutChoiMatrix (Measure.pi (fun _ : S => haarBasisRecords d)) ((d:ℝ)^(Fintype.card S))
      (productRecordedProjector d id) (cardinalityReadoutKernel d id r lam)=radialChoiCombination d r lam :=
  cardinalityReadoutChoi_eq d (haarBasisRecords d) id continuous_id (haarBasisRecords_choi_entries d) r lam

/-- The same original Choi formula follows from the genuine finite Pauli record law. -/
theorem cardinalityPauli_choi {S : Type*} [Fintype S] [DecidableEq S]
    (r : ℕ) (lam : ℕ → ℝ) :
    readoutChoiMatrix (Measure.pi (fun _ : S => pauliBasisRecords)) ((2:ℝ)^(Fintype.card S))
      (productRecordedProjector 2 pauliFullRecord) (cardinalityReadoutKernel 2 pauliFullRecord r lam)=
      radialChoiCombination 2 r lam :=
  cardinalityReadoutChoi_eq 2 pauliBasisRecords pauliFullRecord continuous_of_discreteTopology
    pauliBasisRecords_choi_entries r lam

end CertificationGaussian
