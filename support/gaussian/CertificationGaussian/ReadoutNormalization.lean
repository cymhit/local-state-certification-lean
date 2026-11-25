import CertificationGaussian.ReadoutKernelAlgebra

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- The identity tensor on the actual physical-site coordinate type. -/
theorem wickTensorMatrix_one {S I : Type*} [Fintype S] [DecidableEq S]
    [Fintype I] [DecidableEq I] :
    wickTensorMatrix (fun _ : S => (1 : Matrix I I ℂ))=1 := by
  ext x y
  by_cases h : x=y
  · subst y
    simp [wickTensorMatrix]
  · have hn : ∃ s,x s≠y s := by simpa only [not_forall] using mt funext h
    obtain ⟨s,hs⟩ := hn
    simp only [wickTensorMatrix,Matrix.one_apply,h,ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

/-- Independent complete local records tensorize their exact first-moment normalization. -/
theorem productRecordedProjector_mean_entry {S Ω : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace Ω] (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (hmean : ∀ a b : Fin d,(d:ℂ)*(∫ ω,recordedProjector d (record ω) a b∂μ)=
      (1:Matrix (Fin d) (Fin d) ℂ) a b) (x y : S → Fin d) :
    (d:ℂ)^(Fintype.card S)*(∫ ω,productRecordedProjector d record ω x y∂Measure.pi (fun _ : S => μ))=
      (1:Matrix (S → Fin d) (S → Fin d) ℂ) x y := by
  simp only [productRecordedProjector,wickTensorMatrix]
  rw [integral_fintype_prod_eq_prod (fun (s:S) (ω:Ω) => recordedProjector d (record ω) (x s) (y s))]
  calc
    _ = ∏ s : S,(d:ℂ)*(∫ ω,recordedProjector d (record ω) (x s) (y s)∂μ) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ]
    _ = ∏ s : S,(1:Matrix (Fin d) (Fin d) ℂ) (x s) (y s) := by simp only [hmean]
    _ = _ := congrArg (fun M : Matrix (S → Fin d) (S → Fin d) ℂ => M x y) wickTensorMatrix_one

/-- The actual matrix Bochner integral has the POVM normalization D integral P=I. -/
theorem productRecordedProjector_mean {S Ω : Type*} [Fintype S] [DecidableEq S]
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω] (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (hmean : ∀ a b : Fin d,(d:ℂ)*(∫ ω,recordedProjector d (record ω) a b∂μ)=
      (1:Matrix (Fin d) (Fin d) ℂ) a b) :
    (d:ℝ)^(Fintype.card S) • (∫ ω,productRecordedProjector d record ω∂Measure.pi (fun _ : S => μ))=1 := by
  ext x y
  rw [Matrix.smul_apply,matrix_entry_integral _ _ (productRecordedProjector_continuous d record hr)]
  simpa only [Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_natCast] using
    productRecordedProjector_mean_entry d μ record hmean x y

/-- The complete Haar-basis/outcome product records satisfy the actual normalization, with no supplied twirl premise. -/
theorem haarProductRecordedProjector_mean {S : Type*} [Fintype S] [DecidableEq S]
    (d : ℕ) [NeZero d] :
    (d:ℝ)^(Fintype.card S) • (∫ ω,productRecordedProjector (S:=S) d id ω∂Measure.pi (fun _ : S => haarBasisRecords d))=1 :=
  productRecordedProjector_mean d (haarBasisRecords d) id continuous_id (haarBasisRecords_projector_mean d)

/-- The same genuine normalization for the finite three-Pauli-basis/outcome product records. -/
theorem pauliProductRecordedProjector_mean {S : Type*} [Fintype S] [DecidableEq S] :
    (2:ℝ)^(Fintype.card S) • (∫ ω,productRecordedProjector (S:=S) 2 pauliFullRecord ω∂Measure.pi (fun _ : S => pauliBasisRecords))=1 :=
  productRecordedProjector_mean 2 pauliBasisRecords pauliFullRecord continuous_of_discreteTopology pauliBasisRecords_projector_mean

end CertificationGaussian
